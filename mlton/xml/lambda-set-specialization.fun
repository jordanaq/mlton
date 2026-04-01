(* TODO: Copyrights? *)

(*
 * Perform Lambda Set Specialization on our SXML program. This
 * creates copies of higher-order functions specialized to the
 * lambdas that may be passed to it, creating a first-order
 * function.
 *)
functor LambdaSetSpecialization (S: XML_TRANSFORM_STRUCTS): XML_TRANSFORM =
struct

open S
datatype z = datatype Dec.t
datatype z = datatype PrimExp.t

structure Graph = DirectedGraph
structure Node = Graph.Node


fun transform (Program.T {datatypes, body, ...}): Program.t =
let
  type lsArgId = Var.t
  type lsArgToType = (lsArgId * Type.t) vector
  type conToLsArgs = (Con.t * lsArgId vector) vector

  (* TODO: Swap to use something other than Var *)
  fun newLsArg () = Var.newString "ls_arg_"

  (* datatype -> Con.t to LS arg IDs vector *)
  val {get = getDatatypeAnnotations: Tycon.t -> conToLsArgs option,
       set = setDatatypeAnnotations, ...} =
    Property.getSetOnce (Tycon.plist, Property.initConst NONE)

  (* constructor -> LS arg ID LS arg ID & type IDs *)
  val {get = getConAnnotations: Con.t -> lsArgToType option,
       set = setConAnnotations, ...} =
    Property.getSetOnce (Con.plist, Property.initConst NONE)

  (*
   * LS arg id -> set of possible lambads
   * TODO: check memory-safeness
   *)
  val {get = getLsArgLambdas: lsArgId -> Lambda.t list ref, ...} =
    Property.get (Var.plist, Property.initFun (fn _ => ref []))

  fun addLambdaToLsArg (lsArg: lsArgId, lambda: Lambda.t): unit =
    let
      val lambdas = getLsArgLambdas lsArg
    in
      if List.exists (!lambdas, fn l => Lambda.equals (l, lambda))
        then ()
        else List.push (lambdas, lambda)
    end

  (* Create fresh LS args for  arrow-typed subterms in a con arg type *)
  fun collectArrowTypes (t: Type.t): Type.t vector =
    let
      fun f (t: Type.t, acc: Type.t list): Type.t list =
        case Type.dest t of
           Type.Var _ => acc
         | Type.Con (tycon, tys) =>
             let
               (* Do not look for nested arrow types, these will not be
                * specializable
                *)
               val ac = if Tycon.equals (tycon, Tycon.arrow)
                 then t::acc
                 else acc
             in
               Vector.fold (tys, acc, f)
             end
    in
      Vector.fromListRev (f (t, []))
    end
  
  (* Annotate just the explicit arrow types in a datatype's cons *)
  fun annotateDatatype {cons, tycon, ...} =
    let
      val _ = print ("LSS annotating datatype " ^ Tycon.toString tycon ^ "\n")

      fun annotateCon ({arg, con}: {arg: Type.t option, con: Con.t}) =
        let
          val argTypesWithArrows =
            case arg of
               NONE => Vector.new0 ()
             | SOME t => collectArrowTypes t
          val lsArgIds = Vector.map (argTypesWithArrows, fn _ => newLsArg ())

          val _ = print ("  con " ^ Con.toString con ^ " has " ^
                         Int.toString (Vector.length argTypesWithArrows) ^
                         " arrows\n")

          val conAnnotations =
            Vector.map2 (lsArgIds,
                         argTypesWithArrows,
                         fn (lsArg, argTy) => (lsArg, argTy))
          val _ =
            setConAnnotations (con,
                               if Vector.isEmpty conAnnotations
                                 then NONE
                                 else SOME conAnnotations)
          val _ = Vector.foreach (lsArgIds, fn lsArg => ignore (getLsArgLambdas lsArg))
        in
          (con, lsArgIds)
        end

      val datatypeAnnotations = Vector.map (cons, annotateCon)

      val _ = print ("Finished datatype " ^ Tycon.toString tycon ^ "\n")
    in
      setDatatypeAnnotations (tycon, SOME datatypeAnnotations)
    end

  (* g has edges between tycons that have a dependency *)
  val g = Graph.new ()
  val {get = getTyconNode: Tycon.t -> unit Node.t option,
       set = setTyconNode, ...} =
    Property.getSetOnce (Tycon.plist, Property.initConst NONE)

  (* I dont remember why I made two way thing instead of using Tycon.t Node.t *)
  val {get = getNodeTycon: unit Node.t -> Tycon.t,
       set = setNodeTycon, ... } =
    Property.getSetOnce (Node.plist,
                         Property.initRaise
                         ("LambdaSetSpecialization.nodeTycon", Node.layout))
  
  fun ensureTyconNode (tycon: Tycon.t): unit Node.t =
    case getTyconNode tycon of
       SOME node => node
     | NONE => let
                 val node = Graph.newNode g
                 val _ = setTyconNode (tycon, SOME node)
                 val _ = setNodeTycon (node, tycon)
               in
                 node
               end

  fun datatypeHasLsArgs (tycon: Tycon.t): bool =
    case getDatatypeAnnotations tycon of
       NONE => false
     | SOME conMap => Vector.exists (conMap,
                                     fn (_, lsArgs) =>
                                       not (Vector.isEmpty lsArgs))

  fun referencedTyconsInType (t: Type.t): Tycon.t list =
    let
      fun f (ty: Type.t, acc: Tycon.t list): Tycon.t list=
        case Type.dest ty of
           Type.Var _ => acc
         | Type.Con (tycon, tys) =>
             Vector.fold (tys, tycon :: acc, f)
    in
      f (t, [])
    end

  fun addDatatypeEdges {cons, tycon = fromTycon, ...}: unit =
    let
      val _ = print ("LSS datatype graph edges from " ^ Tycon.toString fromTycon ^ "\n")
      val _ =
        if (datatypeHasLsArgs fromTycon)
          then ignore (ensureTyconNode fromTycon)
          else ()

      val referencedTycons =
        Vector.fold (cons, [],
                     fn ({arg, ...}, acc) =>
                       case arg of
                          NONE => acc
                        | SOME t => List.append (referencedTyconsInType t, acc))

      val seen: Tycon.t list ref = ref []
      fun hasSeen tycon = 
        if List.exists (!seen, fn tyconOther => Tycon.equals (tycon, tyconOther))
          then true
          else (ignore (List.push (seen, tycon)); false)


      val _ = List.foreach
        (referencedTycons,
         fn toTycon =>
           if ((not (Tycon.equals (fromTycon, toTycon)))
               andalso datatypeHasLsArgs toTycon
               andalso (not (hasSeen toTycon)))
             then
               let
                 val _ = print("  to " ^ Tycon.toString toTycon ^ "\n")
                 val fromNode = ensureTyconNode fromTycon
                 val toNode = ensureTyconNode toTycon
                 val _ = Graph.addEdge (g, {from = fromNode, to = toNode})
               in 
                 ()
               end
             else ())
      val _ = print ("LSS datatype finished graph edges from " ^ Tycon.toString fromTycon ^ "\n")
    in
      ()
    end

  (* First, annotate the explicit arrow types *)
  val _ = Vector.foreach (datatypes, annotateDatatype)

  (* Add the datatype dependencies to the graph *)
  val _ = Vector.foreach (datatypes, addDatatypeEdges)

  val _ = print ("datatype graph dump begin\n")
  val _ =
    Graph.display
    {graph = g,
     layoutNode = (fn node =>
       let
         val tycon = getNodeTycon node
         val lsLayout =
           case getDatatypeAnnotations tycon of
              NONE => Layout.str "none"
            | SOME conMap =>
                Layout.vector
                  (Vector.map (conMap,
                               fn (con, lsArgs) =>
                                 Layout.seq [Con.layout con,
                                             Layout.str ":",
                                             Layout.vector (Vector.map
                                               (lsArgs, Var.layout))]))
       in
         Layout.seq [Tycon.layout tycon, Layout.str " lsArgs=", lsLayout]
       end),
     display = fn l => print (Layout.toString l ^ "\n")}
  val _ = print ("datatype graph dump end\n")
  
  fun layoutLssTransform (Program.T {datatypes, body, ...}) = ()
in
  Program.T { datatypes = datatypes, body = body }
end

end
