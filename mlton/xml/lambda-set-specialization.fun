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
structure Edge = Graph.Edge



fun transform (Program.T {datatypes, body, ...}): Program.t =
let
  type lsArgId = Var.t
  type lsArgToType = (lsArgId * Type.t) vector
  type conToLsArgs = (Con.t * lsArgId vector) vector
  type funDecInfo = {lambda: Lambda.t,
                     ty: Type.t,
                     var: Var.t}
  
  (* TODO: Switch to more generic sigma/delta *)
  type sigma = Tycon.t
  type delta = Tycon.t list ref

  val debugPrefix = "[lss] "
  fun debug (layoutThunk: unit -> Layout.t): unit =
    Control.diagnostic
      (fn () =>
       let open Layout
       in
         seq [str debugPrefix, layoutThunk ()]
       end)

  (* TODO: Swap to use something other than Var *)
  fun newLsArg () = Var.newString "ls_arg"

  (* datatype -> Con.t to LS arg IDs vector *)
  val {get = getDatatypeAnnotationsMap: Tycon.t -> conToLsArgs option,
       set = setDatatypeAnnotationsMap, ...} =
    Property.getSet (Tycon.plist, Property.initConst NONE)

  (* datatype -> lsArgId list for the ordered list of args a dt takes in *)
  val {get = getDatatypeLsArgs: Tycon.t -> lsArgId list,
       set = setDatatypeLsArgs, ...} =
    Property.getSet (Tycon.plist, Property.initConst [])

  (* constructor -> LS arg ID LS arg ID & type IDs *)
  val {get = getConAnnotations: Con.t -> lsArgToType option,
       set = setConAnnotations, ...} =
    Property.getSetOnce (Con.plist, Property.initConst NONE)

  val {get = getTyconSccMembers: Tycon.t -> Tycon.t list,
       set = setTyconSccMembers, ...} =
    Property.getSetOnce (Tycon.plist, Property.initConst [])

  val {get = getVarLsArg: Var.t -> lsArgId option,
       set = setVarLsArg, ... } =
    Property.getSetOnce (Var.plist, Property.initConst NONE)

  val {get = getFunDec: Var.t -> funDecInfo option,
       set = setFunDec, ...} =
    Property.getSetOnce (Var.plist, Property.initConst NONE)

  val uosFunBoundVars: Var.t list ref = ref []

  val {get = getLsArgFuns: lsArgId -> Var.t list ref, ... } =
    Property.get (Var.plist, Property.initFun (fn _ => ref []))

  fun addLsArgFun (lsArg: lsArgId, f: Var.t): unit =
    let
      val funs = getLsArgFuns lsArg
      val _ = funs := f :: !funs
    in
      ()
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
               val acc = if Tycon.equals (tycon, Tycon.arrow)
                 then t :: acc
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
      val _ =
        debug (fn () =>
          Layout.seq
           [Layout.str "annotating datatype ",
            Tycon.layout tycon,
            Layout.str " with ",
            Int.layout (Vector.length cons),
            Layout.str " constructors"])

      fun annotateCon ({arg, con}: {arg: Type.t option, con: Con.t}) =
        let
          val argTypesWithArrows =
            case arg of
               NONE => Vector.new0 ()
             | SOME t => collectArrowTypes t
          val lsArgIds = Vector.map (argTypesWithArrows, fn _ => newLsArg ())

          val _ =
            debug (fn () =>
              Layout.seq
              [Layout.str "  con ",
               Con.layout con,
               Layout.str " has ",
               Int.layout (Vector.length argTypesWithArrows),
               Layout.str " arrow occurrences"])

          val conAnnotations =
            Vector.map2 (lsArgIds,
                         argTypesWithArrows,
                         fn (lsArg, argTy) => (lsArg, argTy))
          val _ =
            setConAnnotations (con,
                               if Vector.isEmpty conAnnotations
                                 then NONE
                                 else SOME conAnnotations)
          val _ = Vector.foreach (lsArgIds, fn lsArg => ignore (getLsArgFuns lsArg))
        in
          (con, lsArgIds)
        end

      val datatypeAnnotations = Vector.map (cons, annotateCon)

      val _ = debug (fn () => Layout.seq [Layout.str "finished datatype ",
                                          Tycon.layout tycon])
    in
      setDatatypeAnnotationsMap (tycon, SOME datatypeAnnotations)
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

  (* Dumps the graph with an id *)
  fun graphDump (id: string) =
    let
      val _ = debug (fn () => Layout.str ("datatype graph dump " ^ id ^ " begin"))
      val _ =
        Graph.foreachNode (g, fn node =>
          let
            val tycon = getNodeTycon node
            val lsArgs = getDatatypeLsArgs tycon
            val lsArgsLayout = Layout.list (List.map (lsArgs, Var.layout))
            val lsConLayout =
              case getDatatypeAnnotationsMap tycon of
                 NONE => Layout.str "none"
               | SOME conMap =>
                   Layout.vector (Vector.map
                     (conMap, fn (con, lsArgs) =>
                       Layout.seq [Con.layout con,
                                   Layout.str ":",
                                   Layout.vector (Vector.map (lsArgs, Var.layout))]))
          in
            debug (fn () =>
              Layout.seq [Layout.str "  lsArgs ",
                          Tycon.layout tycon,
                          lsArgsLayout,
                          Layout.str " = ",
                          lsConLayout])
          end)
      val _ =
        Graph.display
          {graph = g,
           layoutNode = (fn node => Tycon.layout (getNodeTycon node)),
           display = fn l => debug (fn () =>
             (Layout.seq [Layout.str "  ", l, Layout.str "\n"]))}
      val _ = debug (fn () => Layout.str ("datatype graph dump " ^ id ^ " end"))
    in
      ()
    end
  
  (* Add a node for tycon to the graph if it does not exist *)
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

  (* Sanity check that the vector is not empty *)
  fun datatypeHasLsArgs (tycon: Tycon.t): bool =
    case getDatatypeAnnotationsMap tycon of
       NONE => false
     | SOME conMap => Vector.exists (conMap,
                                     fn (_, lsArgs) =>
                                       not (Vector.isEmpty lsArgs))

  fun datatypeLsArgsByTycon (tycon: Tycon.t): lsArgId list =
    let
      fun f (lsArg: lsArgId, acc: lsArgId list): lsArgId list =
        if List.exists (acc, fn seen => Var.equals (seen, lsArg))
          then acc
          else lsArg :: acc
    in
      case getDatatypeAnnotationsMap tycon of
         NONE => []
       | SOME conMap =>
           List.rev
            (Vector.fold (conMap, [],
                          fn ((_, lsArgs), acc) =>
                            Vector.fold (lsArgs, acc, f)))
    end

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

  (* Adds edges representing dependency between datatypes to the graph *)
  fun addDatatypeEdges {cons, tycon = fromTycon, ...}: unit =
    let
      val _ =
        debug (fn () =>
          Layout.seq
           [Layout.str "Adding graph edges from",
            Tycon.layout fromTycon,
            Layout.str "\n"])
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
                 val fromNode = ensureTyconNode fromTycon
                 val toNode = ensureTyconNode toTycon
                 val _ = Graph.addEdge (g, {from = fromNode, to = toNode})
                 val _ =
                   debug
                   (fn () =>
                    Layout.seq
                    [Layout.str "graph edge ",
                     Tycon.layout fromTycon,
                     Layout.str " -> ",
                     Tycon.layout toTycon])
               in 
                 ()
               end
             else ())
      val _ =
        debug (fn () =>
          Layout.seq
           [Layout.str "Finished graph edges from",
            Tycon.layout fromTycon,
            Layout.str "\n"])
    in
      ()
    end

  fun findDatatypeByTycon (target: Tycon.t) =
    Vector.peek (datatypes, fn {tycon, ...} => Tycon.equals (tycon, target))

  fun addUniqueLsArgRev (lsArg: lsArgId, acc: lsArgId list): lsArgId list =
    if List.exists (acc, fn seen => Var.equals (seen, lsArg))
      then acc
      else lsArg::acc

  fun mergeLsArgsInOrder (base: lsArgId list, extras: lsArgId list): lsArgId list =
    List.rev (List.fold (extras, List.rev base, addUniqueLsArgRev))

  fun freshLsArgsFromTemplate (template: lsArgId list): lsArgId list =
    List.map
      (template,
       fn _ =>
       let
         val lsArg = newLsArg ()
         val _ = ignore (getLsArgFuns lsArg)
       in
         lsArg
       end)


  (* Annotate all the constructors in a list of targets that reference from
   * TODO: This should probably create a new LS ID
   *)
  fun annotateConstructorsReferencingTycons
    (fromTycon: Tycon.t,
     targetTycons: Tycon.t list): unit =
    let
      val propagatedLsArgs =
        List.rev
          (List.fold (targetTycons, [],
                      fn (targetTycon, acc) =>
                        List.fold (getDatatypeLsArgs targetTycon,
                                   acc,
                                   addUniqueLsArgRev)))
      fun isTargetTycon (tycon: Tycon.t): bool =
        List.exists (targetTycons, fn target => Tycon.equals (target, tycon))
      fun referencesTargetTycon (arg: Type.t option): bool =
        case arg of
           NONE => false
         | SOME t => List.exists (referencedTyconsInType t, isTargetTycon)
      fun mergeFresh (existing: lsArgId vector, extras: lsArgId list): lsArgId vector =
        let
          val existing = Vector.toList existing
          val extrasFresh = List.map (extras, fn _ =>
                                              let
                                                val id = newLsArg ()
                                                val _ = ignore (getLsArgFuns id)
                                              in
                                                id
                                              end)
          val merged = mergeLsArgsInOrder (existing, extrasFresh)
        in
          Vector.fromList merged
        end
    in
        case findDatatypeByTycon fromTycon of
           NONE => ()
         | SOME {cons, ...} =>
             let
               val referencingCons =
                 Vector.fold (cons, [],
                              fn ({arg, con}, acc) =>
                                if referencesTargetTycon arg
                                  then con :: acc
                                  else acc)
               fun shouldAnnotateCon (con: Con.t): bool =
                 List.exists (referencingCons, fn c => Con.equals (c, con))
             in
               case getDatatypeAnnotationsMap fromTycon of
                  NONE => ()
                | SOME conMap =>
                    setDatatypeAnnotationsMap
                      (fromTycon,
                       SOME (Vector.map
                         (conMap,
                          fn (con, oldLsArgs) =>
                            if shouldAnnotateCon con
                              then (con, mergeFresh (oldLsArgs, propagatedLsArgs))
                              else (con, oldLsArgs))))
             end
    end
                           

  (* Take into account SCC concerns. TODO: remove redundancy with
   * synchonizeSccTycons
   *)
  fun processDatatypeScc (nodes: unit Node.t list): unit =
    let
      val sccTycons = List.map (nodes, getNodeTycon)

      val _ = debug (fn () =>
        Layout.seq [Layout.str "Processing datatype SCC of ",
                    Layout.list (List.map (sccTycons, Tycon.layout)),
                    Layout.str "\n"])

      val sccLsArgs =
        List.rev (List.fold
          (sccTycons, [],
           fn (tycon, acc) =>
             List.fold (datatypeLsArgsByTycon tycon, acc, addUniqueLsArgRev)))

      (* set the order here *)
      val _ =
        List.foreach (sccTycons, fn tycon =>
          (setDatatypeLsArgs (tycon,sccLsArgs)
           ; setTyconSccMembers (tycon, sccTycons)))

      (* Annotate intra-SCC cons *)
      val _ =
        List.foreach (sccTycons,
                      fn fromTycon =>
                        if List.exists (sccTycons,
                                        fn other =>
                                          not (Tycon.equals (fromTycon, other)))
                          then annotateConstructorsReferencingTycons
                            (fromTycon, sccTycons)
                        else ())

      val _ = debug (fn () => Layout.str "Finished processing datatype SCC")
    in
      ()
    end

  (* Ensure each datatype has the same order and list of ls args as all the
   * other datatypers in its scc
   *)
  fun synchronizeSccTycons (tycon: Tycon.t): unit =
    let
      val sccTycons = getTyconSccMembers tycon
    in
      if List.isEmpty sccTycons
        then ()
        else
          let
            val mergedLsArgs =
              List.rev
                (List.fold (sccTycons, [],
                            fn (memberTycon, acc) =>
                              List.fold
                                (getDatatypeLsArgs memberTycon,
                                acc,
                                addUniqueLsArgRev)))
            val _ =
              List.foreach (sccTycons,
                            fn memberTycon =>
                              setDatatypeLsArgs (memberTycon, mergedLsArgs))
            val _ =
              if List.length sccTycons > 1
                then List.foreach
                  (sccTycons, fn memberTycon =>
                    annotateConstructorsReferencingTycons
                      (memberTycon, sccTycons))
              else ()
          in
            ()
          end
    end

  val seenTycons: Tycon.t list ref = ref []
  fun markSeenTycon tycon = seenTycons := tycon :: !seenTycons
  fun alreadySeenTycon tycon =
    List.exists (!seenTycons, fn seen => Tycon.equals (seen, tycon))

  (* Propagate Ls args requitements upwards, almost as in DFS
   * TODO: PICK UP AND IGNORE SCC MEMBERS WHEN CONSTRUCTING THE
   * datatypeLsArgsByTycon OR WHATEVER WE ARE ASSIGNING VIA setDatatypeLsArgs
   *)
  fun propagateDatatypeLsArgs (fromTycon: Tycon.t): unit =
    if alreadySeenTycon fromTycon
      then ()
      else
        let
          val _ = markSeenTycon fromTycon
          val sccTycons = getTyconSccMembers fromTycon
          fun isSccMember tycon =
            List.exists (sccTycons,
                         fn tyconInScc =>
                           Tycon.equals (tyconInScc, tycon))
        in
          case getTyconNode fromTycon of
             NONE => ()
           | SOME fromNode =>
               let
                 val _ =
                   List.foreach
                     (Node.successors fromNode, fn edge =>
                        let
                          val toTycon = getNodeTycon (Edge.to edge)
                          val _ = propagateDatatypeLsArgs toTycon
                        in
                          if not (isSccMember toTycon)
                            then
                              let
                                val _ =
                                  annotateConstructorsReferencingTycons
                                   (fromTycon, [toTycon])
                                val _ = setDatatypeLsArgs
                                  (fromTycon,
                                   datatypeLsArgsByTycon fromTycon)
                              in
                                ()
                              end
                            else ()
                        end)
                 val _ = synchronizeSccTycons fromTycon
                 val _ = debug (fn () =>
                  Layout.seq [Layout.str "Propagated LS args for ",
                              Tycon.layout fromTycon])
               in
                 ()
               end
        end
  
  fun addUniqueVar (var: Var.t, vars: Var.t list): Var.t list =
    if List.exists (vars, fn v => Var.equals (v, var))
      then vars
      else var :: vars

  fun addFunDeclToLsArg (lsArg: lsArgId, declVar: Var.t): unit =
    let
      val decls = getLsArgFuns lsArg
    in
      if List.exists (!decls, fn existing => Var.equals (existing, declVar))
        then ()
        else List.push (decls, declVar)
    end

  fun typeContainsArrow (t: Type.t): bool =
    let
      fun f ty =
        case Type.dest ty of
           Type.Var _ => false
         | Type.Con (tycon, tys) =>
             Tycon.equals (tycon, Tycon.arrow)
               orelse Vector.exists (tys, f)
    in
      f t
    end

  fun typeIsArrow (t: Type.t): bool =
    case Type.dest t of
       Type.Var _ => false
     | Type.Con (tycon, _) => Tycon.equals (tycon, Tycon.arrow)

  fun typeIsHigherOrder (t: Type.t): bool =
    case Type.dest t of
       Type.Var _ => false
     | Type.Con (tycon, tys) =>
         Tycon.equals (tycon, Tycon.arrow)
           andalso Vector.exists (tys, typeContainsArrow)

  fun maybeAnnotateBoundArrow
    {var: Var.t,
     ty: Type.t,
     funDec: funDecInfo option,
     isUos: bool}: unit =
    if not (typeIsArrow ty)
      then ()
      else
        let
          val _ = debug (fn () => Layout.seq [Layout.str "  Annotating ",
                                              Var.layout var])
          val lsArg = newLsArg ()
          val _ =
            if Option.isNone (getVarLsArg var)
              then ignore (setVarLsArg (var, SOME lsArg)
                           ; addLsArgFun (lsArg, var))
            else ()
          val _ = Option.app (funDec, fn dec => setFunDec (var, SOME dec))
        in
          ()
        end

  fun scanExpForArrowBindings (e: Exp.t): unit =
    let
      val {decs, ...} = Exp.dest e
    in
      List.foreach (decs, scanDecForArrowBindings)
    end

  and scanDecForArrowBindings (d: Dec.t): unit =
    case d of
       MonoVal {exp, ty, var} =>
         (maybeAnnotateBoundArrow {var = var,
                                   ty = ty,
                                   funDec = NONE,
                                   isUos = false}
          ; scanPrimExpForArrowBindings exp)
     | PolyVal {exp, ty, var, ... } =>
         (maybeAnnotateBoundArrow {var = var,
                                   ty = ty,
                                   funDec = NONE,
                                   isUos = false}
          ; scanExpForArrowBindings exp)
     | Exception _ => ()
     | Fun {anns, decs, ...} =>
         let
           val isUos =
             case anns of
                NONE => false
              | SOME annotations => List.exists (annotations, fn a => a = "UOS")
         in
           Vector.foreach (decs,
                           fn (dec as {lambda, ty, var}: funDecInfo) =>
                             (maybeAnnotateBoundArrow {var = var,
                                                       ty = ty,
                                                       funDec = SOME dec,
                                                       isUos = isUos}
                              ; scanLambdaForArrowBindings lambda))
         end

  and scanPrimExpForArrowBindings (e: PrimExp.t): unit =
    case e of
       PrimExp.Lambda l => scanLambdaForArrowBindings l
     | PrimExp.Handle {try, handler, ...} =>
         (scanExpForArrowBindings try; scanExpForArrowBindings handler)
     | PrimExp.Case {cases, default, ...} =>
         (Cases.foreach (cases, scanExpForArrowBindings)
          ; Option.app (default, scanExpForArrowBindings))
     | _ => ()
     (* TODO: check other PrimExp cases *)

  and scanLambdaForArrowBindings (l: Lambda.t): unit =
    let
      val {body, ...} = Lambda.dest l
    in
      scanExpForArrowBindings body
    end

  (* First, annotate the explicit arrow types *)
  val _ = Vector.foreach (datatypes, annotateDatatype)

  (* Add the datatype dependencies to the graph *)
  val _ = Vector.foreach (datatypes, addDatatypeEdges)
  val _ = graphDump "pre elaboration"

  (* Look at each SCC for ls arg reqs *)
  val sccs = Graph.stronglyConnectedComponents g
  val _ = List.foreach (sccs, processDatatypeScc)
  val _ = graphDump "SCC init analysis"

  (* Propagate LS args bottom up *)
  val _ = Graph.foreachNode
    (g, fn node => propagateDatatypeLsArgs (getNodeTycon node))
  val _ = graphDump "Ls arg propagation"

  (* Annotate arrow bindings with ls *)
  val _ = debug (fn () => Layout.str "Beginning exp annotations")
  val _ = scanExpForArrowBindings body
  val _ = debug (fn () => Layout.str "Finished exp annotations")


in
  Program.T { datatypes = datatypes, body = body }
end

end
