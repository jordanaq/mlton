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


(* TODO: Use other than Var.t for lambda set arguments *)
type lsArgId = Var.t

(* Wrapper for types to carry lsArgId *)
datatype typeInfo = T of {ty: typeAux, lsArgs: lsArgId list option}
and typeAux =
   VarA of Tyvar.t
 | ConA of Tycon.t * typeInfo vector

local
  open Layout
in
  fun layoutTypeInfo (T {ty, lsArgs}) =
    seq [layoutTypeAux ty,
         (case lsArgs of NONE => empty
                       | SOME a => seq [str " <", List.layout Var.layout a, str ">"])]

  and layoutTypeAux tyaux =
    case tyaux of
       VarA v => Tyvar.layout v
     | ConA (tc, infos) =>
         if Tycon.equals (tc, Tycon.tuple) andalso Vector.isEmpty infos then
           str "unit"
         else
           seq [Tycon.layout tc,
                (if Vector.length infos = 0 then empty
                 else seq [str "(", Layout.vector (Vector.map (infos, layoutTypeInfo)), str ")"])]
end

fun varNameEq (v1, v2) =
  String.equals (Var.toString v1, Var.toString v2) (* maybe originalName? *)

structure TypeAux =
struct
  datatype t = datatype typeAux
  (* val layout = layoutTypeAux *)
end

(* Wrap typeInfo in structure *)
structure TypeInfo =
struct
  datatype t = datatype typeInfo
  val layout = layoutTypeInfo

  fun makeVar {tyvar: Tyvar.t} =
    T {ty = VarA tyvar, lsArgs = NONE}

  fun makeCon {tycon: Tycon.t, tyInfos: typeInfo vector} =
    T {ty = ConA (tycon, tyInfos), lsArgs = NONE}

  fun makeConAll {tycon: Tycon.t, tyInfos: typeInfo vector, lsArgs: lsArgId list option} =
    T {ty = ConA (tycon, tyInfos), lsArgs = lsArgs}

  fun makeUnit () =
    makeCon {tycon = Tycon.tuple, tyInfos = Vector.new0 ()}

  fun ty (T {ty, ...}): TypeAux.t = ty

  (* Maps the occurences of the old ls args to the new ones *)
  fun mapLsArgs (T {ty, lsArgs}, lsArgMap: lsArgId -> lsArgId): t =
    (* TODO: zip lsArgs with newLsArgs and map all occurrences of old in type with new from zipped pair *)
  let
    val newLsArgs =
      case lsArgs of
         SOME lsArgs => SOME (List.map (lsArgs, lsArgMap))
       | NONE => NONE

    val newTy =
      case ty of
         VarA v => VarA v
       | ConA (tc, infos) =>
           ConA (tc, Vector.map (infos, fn info => mapLsArgs (info, lsArgMap)))
  in
    T {ty = newTy, lsArgs = newLsArgs}
  end

  fun flatLsArgs (T {ty, lsArgs}): lsArgId list =
    case (lsArgs, ty) of
       (NONE, VarA _) => []
     | (SOME lsArgs, VarA _) => lsArgs
     | (NONE, ConA (_, typeInfo)) => List.concatMap (Vector.toList typeInfo, flatLsArgs)
     | (SOME lsArgs, ConA (_, typeInfo)) =>
         List.append (List.concatMap (Vector.toList typeInfo, flatLsArgs), lsArgs)


  (* Check f on lsArgs *)
  fun equalsF (f: (lsArgId list option * lsArgId list option) -> bool)
              (T {ty = ty1, lsArgs = lsArgs1},
               T {ty = ty2, lsArgs = lsArgs2}) =
    case (ty1, ty2) of
       (VarA v1, VarA v2) => Tyvar.equals (v1, v2)
     | (ConA (tc1, infos1), ConA (tc2, infos2)) =>
         Tycon.equals (tc1, tc2) andalso
         f (lsArgs1, lsArgs2) andalso
         Vector.equals (infos1, infos2, equalsF f)
     | _ => false

  (* Don't check lsArgs for equality *)
  fun equals (t1, t2) =
    equalsF (fn (_, _) => true) (t1, t2)

  fun equalsWithLsArgs (t1, t2) =
    equalsF
      (fn (lsArgs1, lsArgs2) =>
         case (lsArgs1, lsArgs2) of
            (NONE, NONE) => true
          | (SOME a1, SOME a2) => List.forall (List.zip (a1, a2), varNameEq)
          | _ => false)
      (t1, t2)
end

(* Wrap VarExp.t to carry ls args *)
structure VarAux =
struct
  datatype t =
    T of {
      var: VarExp.t,
      asLsArg: lsArgId option,
      passedLsArgs: lsArgId list option
    }

    fun make (var: VarExp.t) = T {var = var, asLsArg = NONE, passedLsArgs = NONE}

    fun dest (T varAux) = varAux

    fun var (T {var, ...}) = var

    fun varVar (T {var, ...}) = VarExp.var var

    fun asLsArg (T {asLsArg, ...}) = asLsArg

    fun passedLsArgs (T {passedLsArgs, ...}) = passedLsArgs

    fun equals (T {var = v1, ...},
                T {var = v2, ...}) =
      varNameEq (VarExp.var v1, VarExp.var v2)

    local
      open Layout
    in
      fun layout (T {var, asLsArg, passedLsArgs}) =
        seq [VarExp.layout var,
             (case asLsArg of NONE => empty | SOME a => seq [str " @as(", Var.layout a, str ")"]),
             (if Option.isNone passedLsArgs then empty
              else seq [str " @passed", List.layout Var.layout (Option.valOf passedLsArgs)])]
    end
end

(* Carries LsArgs for a lambda *)
structure LambdaInfo =
struct
  datatype t =
    T of {
      var: Var.t,
      ty: Type.t option,
      isDef: bool ref,
      isUoS: bool ref,
      lsArgs: lsArgId list ref
    }

  local
    open Layout
  in
    fun layout (T {var, ty, isDef, isUoS, lsArgs}) =
      seq [Var.layout var,
           (case ty of NONE => empty | SOME t => seq [str ":", Type.layout t]),
           (if !isDef then str " def" else empty),
           (if !isUoS then str " uos" else empty),
           (if List.isEmpty (!lsArgs) then empty
            else seq [str " lsArgs=", List.layout Var.layout (!lsArgs)])]
  end
end

(* Wrap Con.t to carry ls args *)
structure ConInfo =
struct
  datatype t =
    T of {
      con: Con.t,
      ty: Type.t option,
      lsArgs: lsArgId list
    }

  fun make (con: Con.t, ty: Type.t option) =
    T {con = con, ty = ty, lsArgs = []}

  (*
  fun makeWithLsArgs (con: Con.t, ty: Type.t option, lsArgs: lsArgId list) =
    T {con = con, ty = ty, lsArgs = lsArgs}
   *)

  fun setLsArgs (T {con, ty, ...}, lsArgs) =
    T {con = con, ty = ty, lsArgs = lsArgs}

  fun dest (T conInfo) = conInfo

  (*
  fun con (T {con, ...}) = con

  fun ty (T {ty, ...}) = ty
   *)

  local
    open Layout
  in
    fun layout (T {con, ty, lsArgs}) =
      seq [Con.layout con,
           (case ty of NONE => empty | SOME t => seq [str ":", Type.layout t]),
           (if List.isEmpty lsArgs then empty
            else seq [str " lsArgs=", List.layout Var.layout lsArgs])]
  end
end

(* Wrap Exp.t to carry ls args *)
datatype expAux =
    ExpA of {decs: decAux list,
             result: VarExp.t}
             
and primExpAux =
    AppA of {func: VarAux.t,
             arg: VarExp.t}
  | CaseA of {test: VarExp.t,
              cases: (Pat.t, expAux) Cases.t,
              default: expAux option}
  | ConAppA of {con: ConInfo.t,
                targs: Type.t vector,
                arg: VarExp.t option}
  | ConstA of Const.t
  | HandleA of {try: expAux,
                catch: Var.t * Type.t,
                handler: expAux}
  | LambdaA of lambdaAux
  | PrimAppA of {args: VarExp.t vector,
                 prim: Type.t Prim.t,
                 targs: Type.t vector}
  | ProfileA of ProfileExp.t
  | RaiseA of {exn: VarExp.t, extend: bool}
  | SelectA of {tuple: VarExp.t,
                offset: int}
  | TupleA of VarExp.t vector 
  | VarA of VarExp.t

and decAux =
    ExceptionA of {arg: Type.t option,
                   con: Con.t}
  | FunA of {decs: {lambda: lambdaAux,
                    ty: Type.t,
                    var: Var.t} vector,
             anns: string list option,
             tyvars: Tyvar.t vector,
             asLsArg: lsArgId option,
             passedLsArgs: lsArgId list,
             plist: PropertyList.t}
  | MonoValA of {exp: primExpAux,
                 ty: Type.t,
                 var: Var.t}
    (* PolyValA shouldnt appear *)
  | PolyValA of {exp: expAux,
                 ty: Type.t,
                 tyvars: Tyvar.t vector,
                 var: Var.t}

and lambdaAux = LamA of {arg: Var.t,
                         argType: Type.t,
                         body: expAux,
                         mayInline: bool,
                         plist: PropertyList.t}


local
  open Layout
in
  fun layoutPrimExpAux pe =
    case pe of
       AppA {func, arg} =>
         seq [VarAux.layout func, str " ", VarExp.layout arg]
     | CaseA {test, cases, default} =>
       let
         fun doit (v, layoutP) =
           Vector.toListMap
             (v, fn (p, e) =>
              mayAlign [seq [layoutP p, str " =>"],
                        indent (layoutExpAux e, 3)])
         datatype z = datatype Cases.t
         val cases =
           case cases of
              Con v => doit (v, Pat.layout)
            | Word (_, v) => doit (v, fn w => WordX.layout (w, {suffix = true}))
         val cases =
           case default of
              NONE => cases
            | SOME e => cases @ [mayAlign [str "_ =>", indent (layoutExpAux e, 3)]]
       in
         align [seq [str "case ", VarExp.layout test, str " of"],
                indent (alignPrefix (cases, "| "), 2)]
       end
     | ConAppA {con, targs, arg} =>
         seq [str "con ", ConInfo.layout con,
              (if Vector.length targs = 0 then empty else seq [str " ", Layout.vector (Vector.map (targs, Type.layout))]),
              (case arg of NONE => empty | SOME a => seq [str " ", VarExp.layout a])]
     | ConstA c => Const.layout c
     | HandleA {try, catch, handler} =>
         mayAlign [layoutExpAux try,
                   mayAlign [seq [str "handle ",
                                  Var.layout (#1 catch),
                                  Type.layout (#2 catch),
                                  str " =>"],
                             indent (layoutExpAux handler, 2)]]
     | LambdaA l => layoutLambdaAux l
     | PrimAppA {args, prim, targs} =>
         seq [str "prim ", Prim.layoutFull (prim, Type.layout),
              (if Vector.length targs = 0 then empty else seq [str " ", Layout.vector (Vector.map (targs, Type.layout))]),
              str " ", Vector.layout VarExp.layout args]
     | ProfileA p => ProfileExp.layout p
     | RaiseA {exn, extend} =>
         seq [str "raise ", VarExp.layout exn, str (if extend then " extend" else "")]
     | SelectA {tuple, offset} =>
         seq [str "#", Int.layout offset, str " ", VarExp.layout tuple]
     | TupleA vec => Vector.layout VarExp.layout vec
     | VarA v => VarExp.layout v

  and layoutDecAux dec =
    case dec of
       ExceptionA {arg, con} =>
         seq [str "exception ", Con.layout con,
              (case arg of NONE => empty | SOME t => seq [str " of ", Type.layout t])]
     | FunA {decs, anns, asLsArg, passedLsArgs, ...} =>
         let
           val annPart = 
             seq [if anns = NONE
                  then empty
                  else seq [str " __ann__ ",
                            List.layout
                              (fn s => seq [str "\"",
                                           str (String.escapeSML s),
                                           str "\""])
                            (Option.valOf anns),
                            str " "]]

           val lsPart =
             if Option.isNone asLsArg andalso List.isEmpty passedLsArgs then empty
             else seq [str "@lsArgs",
                      (case asLsArg of
                          NONE => empty
                        | SOME a => seq [str " @as(", Var.layout a, str ")"]),
                      (if List.isEmpty passedLsArgs
                       then empty
                       else seq [str " @passed", List.layout Var.layout passedLsArgs]),
                      str " "]

           val head = seq [str "fun", annPart, lsPart, str " "]

           val binds = Vector.toListMap (decs, fn {lambda, ty, var} =>
                        seq [Var.layout var, str " : ",
                             Type.layout ty,
                             str " = ",
                             layoutLambdaAux lambda])
         in
           align (head :: binds)
         end
     | MonoValA {exp, ty, var} =>
         seq [str "val ", Var.layout var, str " : ", Type.layout ty, str " = ", layoutPrimExpAux exp]
     | PolyValA {exp, ty, var, ...} =>
         seq [str "val ", Var.layout var, str " : ", Type.layout ty, str " = ", layoutExpAux exp]

  and layoutExpAux (ExpA {decs, result}) =
    if List.isEmpty decs then VarExp.layout result
    else align [str "let", indent (align (List.map (decs, layoutDecAux)), 2), str "in", indent (VarExp.layout result, 2), str "end"]

  and layoutLambdaAux (LamA {arg, argType, body, mayInline, ...}) =
    mayAlign [seq [str (if not mayInline then "noinline " else ""), Var.layout arg, str " : ", Type.layout argType, str " =>"],
              indent (layoutExpAux body, 2)]
end

(* Wrap decAux in structure *)
structure DecAux =
struct
  datatype t = datatype decAux

  (* We leave FunA as part of DecAux to mimic structure *)
  fun makeFunA {decs, anns, tyvars} =
    FunA {decs = decs,
          anns = anns,
          tyvars = tyvars,
          asLsArg = NONE,
          passedLsArgs = [],
          plist = PropertyList.new ()}

  fun funVars dec =
    case dec of
       FunA {decs, ...} => Vector.toListMap (decs, fn {var, ...} => var)
     | _ => Error.bug "LambdaSetSpecialization.DecAux.funVars: non-fun"

  fun plist dec =
    case dec of
       FunA {plist, ...} => plist
     | _ => Error.bug "LambdaSetSpecialization.DecAux.plist: non-fun"

  val layout = layoutDecAux

  fun equals (dec1, dec2) =
    case (dec1, dec2) of
       (FunA {decs = decs1, ...},
        FunA {decs = decs2, ...}) =>
         (* Just vars is enough as we want equality on different plist and ls args *)
         Vector.equals (decs1, decs2,
                        fn ({var = var1, ...},
                            {var = var2, ...}) =>
                             varNameEq (var1, var2))
     | _ => false
end

(* Wrap primExpAux in structure *)
structure PrimExpAux =
struct
  datatype t = datatype primExpAux

  val layout = layoutPrimExpAux
end

(* Wrap expAux in structure *)
structure ExpAux =
struct
  datatype t = datatype expAux
  type casesAux = (Pat.t, t) Cases.t

  fun make {decs, result} = ExpA {decs = decs, result = result}

  fun dest (ExpA exp) = exp

  fun decs (ExpA {decs, ...}) = decs
  fun result (ExpA {result, ...}) = result

  val layout = layoutExpAux
end

(* Wrap lambdaAux in structure *)
structure LambdaAux =
struct
  datatype t = datatype lambdaAux

  fun dest (LamA lambda) = lambda

  fun make {arg, argType, body, mayInline, plist} =
    LamA {arg = arg, argType = argType, body = body, mayInline = mayInline, plist = plist}

  val layout = layoutLambdaAux
end
  
(* Debugging helper *)
fun debug (layoutThunk: unit -> Layout.t): unit =
let
  val debugPrefix = "[lss] "
in
  Control.diagnostic
    (fn () =>
     let open Layout
     in
       seq [str debugPrefix, layoutThunk ()]
   end)
end

(* Transform an SXML program via LSS *)
fun transform (Program.T {datatypes, body, ...}): Program.t =
let
  (* TODO: Swap to use something other than Var *)
  fun newLsArg () = Var.newString "ls_arg"

  (* datatype -> Con.t to LS arg IDs vector *)
  val {get = getDatatypeAnnotationsMap: Tycon.t -> (Con.t * lsArgId vector) vector option,
       set = setDatatypeAnnotationsMap, ...} =
    Property.getSet (Tycon.plist, Property.initConst NONE)

  (* datatype -> lsArgId list for the ordered list of args a dt takes in *)
  val {get = getDatatypeLsArgs: Tycon.t -> lsArgId list,
       set = setDatatypeLsArgs, ...} =
    Property.getSet (Tycon.plist, Property.initConst [])

  val {get = getConTycon: Con.t -> Tycon.t,
       set = setConTycon, ...} =
    Property.getSetOnce (Con.plist, Property.initRaise
                         ("LambdaSetSpecialization.conTycon", Con.layout))

  (* Tycon to list of tycons in an SCC *)
  val {get = getTyconSccMembers: Tycon.t -> Tycon.t list,
       set = setTyconSccMembers, ...} =
    Property.getSetOnce (Tycon.plist, Property.initConst [])
  
  fun getLsArgsFromCon (con: Con.t): lsArgId list =
  let
    val tycon = getConTycon con
  in
    case getDatatypeAnnotationsMap tycon of
       NONE => []
     | SOME conMap =>
         case Vector.peek (conMap, fn (conOther, _) => Con.equals (con, conOther)) of
            NONE => []
          | SOME (_, lsArgs) => Vector.toList lsArgs
  end

  fun tyconIsArrow (tycon: Tycon.t): bool =
    Tycon.equals (tycon, Tycon.arrow)

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
             val acc = if tyconIsArrow tycon
               then t :: acc
               else acc
           in
             Vector.fold (tys, acc, f)
           end
  in
    Vector.fromListRev (f (t, []))
  end
  
  (* Annotate just the explicit arrow types in a datatype's cons *)
  fun annotateDatatype ({cons, tycon, ...}: {cons: {arg: Type.t option,
                                                    con: Con.t} vector,
                                             tycon: Tycon.t,
                                             tyvars: Tyvar.t vector})
      : unit =
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
        
        val _ = setConTycon (con, tycon)
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
  fun datatypeHasLsArg (tycon: Tycon.t): bool =
    case getDatatypeAnnotationsMap tycon of
       NONE => false
     | SOME conMap => Vector.exists (conMap,
                                     fn (_, lsArgs) =>
                                       not (Vector.isEmpty lsArgs))

  (* Accumulates lsArgs from the list of constructors *)
  fun datatypeLsArgsByTycon (tycon: Tycon.t): lsArgId list =
  let
    fun f (lsArg: lsArgId, acc: lsArgId list): lsArgId list =
      if List.exists (acc, fn seen => varNameEq (seen, lsArg))
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
  
  (* Get the list of tycons referenced in type *)
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

    (* Ensure a node if fromTycon has ls args *)
    val _ =
      if (datatypeHasLsArg fromTycon)
        then ignore (ensureTyconNode fromTycon)
        else ()

    (* Accumulate all referenced tycons *)
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

    (* Create an edge when fromTycon references a toTycon with lsArgs *)
    val _ = List.foreach
      (referencedTycons,
       fn toTycon =>
         if ((not (Tycon.equals (fromTycon, toTycon)))
             andalso datatypeHasLsArg toTycon
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

  (* Get the unique datatype associated with `target` *)
  fun findDatatypeByTycon (target: Tycon.t) =
    Vector.peek (datatypes, fn {tycon, ...} => Tycon.equals (tycon, target))

  (* Prepend lsArg if not in acc *)
  fun addUniqueLsArgRev (lsArg: lsArgId, acc: lsArgId list): lsArgId list =
    if List.exists (acc, fn seen => varNameEq (seen, lsArg))
      then acc
      else lsArg::acc

  (* Adds extras to base list of lsArgs *)
  fun mergeLsArgsInOrder (base: lsArgId list, extras: lsArgId list): lsArgId list =
    List.rev (List.fold (extras, List.rev base, addUniqueLsArgRev))

  (* Freshens a list of ls args *)
  fun freshLsArgsFromTemplate (template: lsArgId list): lsArgId list =
    List.map
      (template,
       fn _ =>
       let
         val lsArg = newLsArg ()
       in
         lsArg
       end)


  (* Annotate all the constructors in a list of targets that reference from *)
  fun annotateConstructorsReferencingTycons
    (fromTycon: Tycon.t,
     targetTycons: Tycon.t list,
     isIntraScc: bool): unit =
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

    (* merge two lists of ls args but freshen if existing and extras dont
     * share an scc
     *)
    fun mergeFresh (existing: lsArgId vector, extras: lsArgId list): lsArgId vector =
    let
      val merged = if isIntraScc
        then extras
        else
          let
            val existing = Vector.toList existing
            val extrasFresh =
              List.map (extras, fn _ =>
                                let
                                  val id = newLsArg ()
                                in
                                  id
                                end)
          in
            mergeLsArgsInOrder (existing, extrasFresh)
          end
    in
      Vector.fromList merged
    end
  in
    case findDatatypeByTycon fromTycon of
       NONE => () (* Unreachable *)
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
                           

  (* Create tycon to scc map and initial scc annotations *)
  fun processDatatypeScc (nodes: unit Node.t list): unit =
  let
    val sccTycons = List.map (nodes, getNodeTycon)

    val _ = debug (fn () =>
      Layout.seq [Layout.str "Processing datatype SCC of ",
                  Layout.list (List.map (sccTycons, Tycon.layout)),
                  Layout.str "\n"])

    (* Every item in an scc shares args *)
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
                    (memberTycon, sccTycons, true))
            else ()
        in
          ()
        end
  end

  fun propagateDatatypeLsArgs (): unit =
  let
    (* Mutable to simplify implementation *)
    val seenTycons: Tycon.t list ref = ref []
    fun markSeenTycon tycon = seenTycons := tycon :: !seenTycons
    fun alreadySeenTycon tycon =
      List.exists (!seenTycons, fn seen => Tycon.equals (seen, tycon))

    (* Propagate Ls args requitements upwards, ensuring SCC syncing *)
    fun propagateDatatypeLsArgsH (fromTycon: Tycon.t): unit =
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
                          val _ = propagateDatatypeLsArgsH toTycon
                        in
                          if not (isSccMember toTycon)
                            then
                              let
                                val _ =
                                  annotateConstructorsReferencingTycons
                                   (fromTycon, [toTycon], false)
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
  in
    Graph.foreachNode
      (g, fn node => propagateDatatypeLsArgsH (getNodeTycon node))
  end
  
  fun typeIsArrow (t: Type.t): bool =
    case Type.dest t of
       Type.Var _ => false
     | Type.Con (tycon, _) => tyconIsArrow tycon

  (* map from var to containing dec *)
  val {get = getDecFromVar: Var.t -> DecAux.t option,
       set = setDecFromVar, ...} =
    Property.getSetOnce (Var.plist, Property.initConst NONE)

  (* Check if ann is in anns list of DecAux *)
  fun isAnnotatedBuilder(ann: string): DecAux.t -> bool =
    fn (dec: DecAux.t) =>
      case dec of
         FunA {anns, ...} =>
           (case anns of
               SOME anns =>
               (not (List.isEmpty anns))
                 andalso List.contains (anns, ann, String.equals)
             | NONE => false)
       | _ => false

  (* Get the type of a Con's arg*)
  fun conToType (con: Con.t): Type.t option =
  let
    val tycon = getConTycon con

    val {cons, ...} =
      case findDatatypeByTycon tycon of
         NONE => Error.bug "LambdaSetSpecialization.conToType: no datatype for con's tycon"
       | SOME dt => dt

    val ty =
      case Vector.peek (cons, fn {con = conOther, ...} => Con.equals (con, conOther)) of
         NONE => Error.bug "LambdaSetSpecialization.conToType: con not found in its datatype"
       | SOME {arg, ...} => arg
  in
    ty
  end

  (* Are Defs are the same as in the paper and UoS are what Defs specialize on *)
  val isDef = isAnnotatedBuilder "def"
  val isUoS = isAnnotatedBuilder "uos"

  type Def = DecAux.t
  type Defs = Def list
  type UoSs = Def list

  (* Build our auxiliary structure tracking ls args, gathering defs, uoss *)
  fun expToAux (exp: Exp.t):
      {aux: ExpAux.t, defs: Defs, uoss: UoSs} =
  let
    (* Store def and uos decs *)
    val defs: Defs ref = ref []
    val uoss: UoSs ref = ref []

    (* Add dec to list of defs if def*)
    fun addDef (dec: DecAux.t): unit =
      if isDef dec then ignore (List.push (defs, dec)) else ()

    (* Add dec to list of UoSs if UoS *)
    fun addUoS (dec: DecAux.t): unit =
      if isUoS dec then ignore (List.push (uoss, dec)) else ()

    (* Map from all vars in dec to dec *)
    fun addVarToDec (dec: DecAux.t): unit =
    let
      val vars = DecAux.funVars dec
    in
      List.foreach (vars, fn var => setDecFromVar (var, SOME dec))
    end

    (* Create ExpAux from Exp *)
    fun handleExp (exp: Exp.t) =
    let
      val {decs, result} = Exp.dest exp
      val decs = List.map (decs, handleDec)
    in
      ExpA {decs = decs, result = result}
    end

    (* Create PrimExpAux from PrimExp *)
    and handlePrimExp (primExp: PrimExp.t) =
      case primExp of
         PrimExp.App {func, arg, ...} =>
           AppA {func = VarAux.make func, arg = arg}
       | PrimExp.Case {test, cases, default, ...} =>
         let
           (* Get aux cases *)
           val cases =
             case cases of
                Cases.Con v =>
                  Cases.Con
                    (Vector.map (v, fn (pat, exp) => (pat, handleExp exp)))
              | Cases.Word (ws, v) =>
                  Cases.Word
                    (ws,
                     Vector.map (v, fn (pat, exp) => (pat, handleExp exp)))

           val default =
             case default of
                SOME exp => SOME (handleExp exp)
              | NONE => NONE
         in
           CaseA {test = test, cases = cases, default = default}
         end
       | PrimExp.ConApp {con, targs, arg, ...} =>
           ConAppA {con = ConInfo.make (con, conToType con), targs = targs, arg = arg}
       | PrimExp.Const const => ConstA const
       | PrimExp.Handle {try, catch, handler, ...} =>
         let
           val try = handleExp try
           val handler = handleExp handler
         in
           HandleA {try = try, catch = catch, handler = handler}
         end
       | PrimExp.Lambda lambda => LambdaA (handleLambda lambda)
       | PrimExp.PrimApp {args, prim, targs, ...} =>
           PrimAppA {args = args, prim = prim, targs = targs}
       | PrimExp.Profile profile => ProfileA profile
       | PrimExp.Raise {exn, extend, ...} => RaiseA {exn = exn, extend = extend}
       | PrimExp.Select {tuple, offset, ...} => SelectA {tuple = tuple, offset = offset}
       | PrimExp.Tuple tuple => TupleA tuple
       | PrimExp.Var var => VarA var

    (* Create DecAux from Dec *)
    and handleDec (dec: Dec.t) =
      case dec of
         Dec.Exception {arg, con, ...} => ExceptionA {arg = arg, con = con}
       | Dec.Fun {decs, anns, tyvars, ...} =>
         let
           (* create aux for one binding in block *)
           fun f ({lambda, ty, var, ...}: {lambda: Lambda.t, ty: Type.t, var: Var.t}) =
             {lambda = handleLambda lambda,
              ty = ty,
              var = var}

           (* create aux for each binding *)
           val decs = Vector.map (decs, f)

           (* Create DecAux *)
           val ret = DecAux.makeFunA {decs = decs, anns = anns, tyvars = tyvars}

           (* Check annotations for def/uos *)
           val _ = addDef ret
           val _ = addUoS ret

           (* Map all the vars to the dec aux with same ls args ref *)
           val _ = addVarToDec ret
         in
           ret
         end
       | Dec.MonoVal {exp, ty, var, ...} =>
           MonoValA {exp = handlePrimExp exp, ty = ty, var = var}
       | Dec.PolyVal _ =>
           Error.bug "LambdaSetSpecialization.handleDec: Encountered PolyVal at SXML"

    (* Create LambdaAux from Lambda *)
    and handleLambda (lambda: Lambda.t) =
    let
      val {arg, argType, body, mayInline, ...} = Lambda.dest lambda
      val plist = Lambda.plist lambda
    in
      LamA {arg = arg,
            argType = argType,
            body = handleExp body,
            mayInline = mayInline,
            plist = plist}
    end

    val aux = handleExp exp
  in
    {aux = aux, defs = !defs, uoss = !uoss}
  end

  (* Get Exp from ExpAux *)
  fun auxToExp (exp: ExpAux.t): Exp.t =
  let
    (* Simple deconstruction *)

    fun handleExp (ExpA {decs, result}) =
    let
      val decs = List.map (decs, handleDec)
    in
      Exp.make {decs = decs, result = result}
    end

    and handlePrimExp (primExp) =
      case primExp of
         AppA {func, arg, ...} =>
         let
           val VarAux.T {var, ...} = func
         in
           PrimExp.App {func = var, arg = arg}
         end
       | CaseA {test, cases, default, ...} =>
         let
           val cases =
             case cases of
                Cases.Con v =>
                  Cases.Con
                    (Vector.map (v, fn (pat, exp) => (pat, handleExp exp)))
              | Cases.Word (ws, v) =>
                  Cases.Word
                    (ws,
                     Vector.map (v, fn (pat, exp) => (pat, handleExp exp)))
           val default =
             case default of
                SOME exp => SOME (handleExp exp)
              | NONE => NONE
         in
           PrimExp.Case {test = test, cases = cases, default = default}
         end
       | ConAppA {con, targs, arg, ...} =>
         let
           val {con, ...} = ConInfo.dest con
         in
           PrimExp.ConApp {con = con, targs = targs, arg = arg}
         end
       | ConstA const => PrimExp.Const const
       | HandleA {try, catch, handler, ...} =>
         let
           val try = handleExp try
           val handler = handleExp handler
         in
           PrimExp.Handle {try = try, catch = catch, handler = handler}
         end
       | LambdaA lambda => PrimExp.Lambda (handleLambda lambda)
       | PrimAppA {args, prim, targs, ...} =>
           PrimExp.PrimApp {args = args, prim = prim, targs = targs}
       | ProfileA profile => PrimExp.Profile profile
       | RaiseA {exn, extend, ...} => PrimExp.Raise {exn = exn, extend = extend}
       | SelectA {tuple, offset, ...} => PrimExp.Select {tuple = tuple, offset = offset}
       | TupleA tuple => PrimExp.Tuple tuple
       | VarA var => PrimExp.Var var

    and handleDec (dec) =
      case dec of
         ExceptionA {arg, con, ...} => Dec.Exception {arg = arg, con = con}
       | FunA {decs, anns, tyvars, ...} =>
         let
           fun f ({lambda, ty, var, ...}) =
             {lambda = handleLambda lambda,
              ty = ty,
              var = var}

           val decs = Vector.map (decs, f)
         in
           Dec.Fun {decs = decs, anns = anns, tyvars = tyvars}
         end
       | MonoValA {exp, ty, var, ...} =>
           Dec.MonoVal {exp = handlePrimExp exp, ty = ty, var = var}
       | PolyValA _ =>
           (* Dec.PolyVal {exp = handleExp exp, ty = ty, tyvars = tyvars, var = var} *)
           Error.bug "LambdaSetSpecialization.auxToExp.handleDec: Encountered PolyValA at SXML"

    and handleLambda (lambda) =
    let
      val {arg, argType, body, mayInline, plist, ...} = LambdaAux.dest lambda
    in
      Lambda.makeInternal
        {arg = arg,
         argType = argType,
         body = handleExp body,
         mayInline = mayInline,
         plist = plist}
    end
  in
    handleExp exp
  end

  (* Map var owner (bound in dec) to type information. This works thanks to SXML invariants *)
  val {get = getTyInfoFromVar: Var.t -> TypeInfo.t option,
       set = setTyInfoFromVar, ...} =
    Property.getSetOnce (Var.plist, Property.initConst NONE)

  fun getTyInfoFromVarExp (varExp: VarExp.t): TypeInfo.t option =
    getTyInfoFromVar (VarExp.var varExp)

  fun getTyInfoFromVarAux (varAux: VarAux.t): TypeInfo.t option =
    getTyInfoFromVarExp (VarAux.var varAux)

  val {get = getLsArgsFromDec: DecAux.t -> lsArgId list,
       set = setLsArgsFromDec, ...} =
    Property.getSetOnce (DecAux.plist, Property.initConst [])

(* Construct new TypeInfo for Type *)
fun infoFromTy (ty: Type.t): TypeInfo.t =
  case Type.dest ty of
     Type.Var tyvar => TypeInfo.makeVar {tyvar = tyvar}
   | Type.Con (tycon, tys) =>
       let
         val tyInfos = Vector.map (tys, infoFromTy)
         val lsArgs = if typeIsArrow ty
           then SOME [newLsArg ()]
           else let
             val lsArgs = getDatatypeLsArgs tycon
           in 
              if List.isEmpty lsArgs
                then NONE
                else SOME (freshLsArgsFromTemplate lsArgs)
            end
       in
         TypeInfo.makeConAll {tycon = tycon, tyInfos = tyInfos, lsArgs = lsArgs}
       end
  
  fun isInDelta (delta: Var.t list, var: Var.t): bool =
    List.exists (delta, fn v => varNameEq (v, var))

  (* Add an element to a list if it is not already present, via eq *)
  fun addUnique eq (x, acc) =
    if List.contains (acc, x, eq) then acc else x :: acc

  (* Union two lists via an element-wise combining function *)
  fun unionLists f lsts =
  let
    fun g (xs, acc) =
      List.fold (xs, acc, f)
  in
    List.fold (lsts, [], g)
  end

  (* Annotate Aux, carrying out the F function *)
  fun annotateAux (body: ExpAux.t, defs: Defs, uoss: UoSs):
      {aux: ExpAux.t, delta: Var.t list} =
  let
    (* A lot of the original complexity in the algorithm is unnecessary thanks to SXML *)

    (* Annotate our types. Take advantage of the fact that owner is unique to map to info *)
    fun handleTy (owner: Var.t, ty: Type.t, indent: int): Type.t =
    let 
        val _ = debug (fn () =>
          Layout.indent (Layout.seq [Layout.str "Starting type annotation for ",
                                     Var.layout owner], indent))

        val tyInfo = infoFromTy ty

        val _ = case getTyInfoFromVar owner of
               SOME existingInfo =>
                 if TypeInfo.equals (existingInfo, tyInfo)
                   then ()
                   else let
                     val _ = debug (fn () =>
                       Layout.indent (Layout.seq [Layout.str "Conflicting type info for var ",
                                                  Var.layout owner,
                                                  Layout.str "\n\texisting info: ",
                                                  TypeInfo.layout existingInfo,
                                                  Layout.str "\n\tnew info: ",
                                                  TypeInfo.layout tyInfo], indent))
                   in
                     Error.bug "LambdaSetSpecialization.annotateAux.handleTy: conflicting type info for var"
                    end
             | NONE => setTyInfoFromVar (owner, SOME tyInfo)

        val _ = debug (fn () =>
          Layout.indent (Layout.seq [Layout.str "Annotating type of var ",
                                     Var.layout owner,
                                     Layout.str " with info ",
                                     TypeInfo.layout tyInfo], indent))
    in
      ty (* TODO: make unit type return *)
    end

    fun varIsD (var: Var.t, d: Def option): bool =
      case d of
        SOME def => varNameEq (var, List.first (DecAux.funVars def))
      | NONE => false

    (* Annotates VarAux with new ls arg *)
    fun newLsToVarAux (delta: Var.t list,
                       d: Def option,
                       VarAux.T {var, asLsArg, passedLsArgs}: VarAux.t,
                       indent: int): VarAux.t =
    let
      val varI = VarExp.var var

      val asLsArg = SOME (newLsArg ())

      val _ = if Option.isNone passedLsArgs
        then ()
        else Error.bug "LambdaSetSpecialization.transform.annotateAux.newLsToVarAux: unexpected passed ls args"

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Annotating var ",
                                   Var.layout varI], indent))
    in
      if isInDelta (delta, varI) andalso not (varIsD (varI, d))
        then
          let
            val dec = Option.valOf (getDecFromVar varI)
            val lsArgs = getLsArgsFromDec dec
            val freshenedLsArgs = freshLsArgsFromTemplate lsArgs
            val _ = debug (fn () =>
              Layout.indent (Layout.seq [Layout.str "var is in delta, annotating with freshened ls args: ",
                                         List.layout Var.layout freshenedLsArgs], indent))
            val freshenedLsArgs = if List.isEmpty lsArgs
              then NONE
              else SOME freshenedLsArgs
          in
            VarAux.T {var = var, asLsArg = asLsArg, passedLsArgs = freshenedLsArgs}
          end
        else VarAux.T {var = var, asLsArg = asLsArg, passedLsArgs = NONE}
    end

    val unionVarAuxs = unionLists (addUnique VarAux.equals)

    (* Gets all the inner VarAux that need to be annotated for a given exp *)
    fun innerVarAuxInDeltaExp (delta: Var.t list) (d: Def option) (exp: ExpAux.t): VarAux.t list =
      unionVarAuxs (List.map (ExpAux.decs exp, innerVarAuxInDeltaDec delta d))

    and innerVarAuxInDeltaDec (delta: Var.t list) (d: Def option) (dec: DecAux.t): VarAux.t list =
      case dec of
        DecAux.FunA {decs, ...} =>
          unionVarAuxs (Vector.toListMap (decs, fn {lambda, ...} => innerVarAuxInDeltaLambda delta d lambda))
      | DecAux.MonoValA {exp, ...} =>
          innerVarAuxInPrimExp delta d exp
      | DecAux.ExceptionA _ => []
      | DecAux.PolyValA _ => Error.bug "LambdaSetSpecialization.transform.annotateAux.innerVarAuxInDeltaDec: unexpected PolyValA"

    and innerVarAuxInDeltaLambda (delta: Var.t list) (d: Def option) (lambda: LambdaAux.t): VarAux.t list =
      case lambda of
        LambdaAux.LamA {body, ...} =>
          innerVarAuxInDeltaExp delta d body

    and innerVarAuxInPrimExp (delta: Var.t list) (d: Def option) (primExp: PrimExpAux.t): VarAux.t list =
      case primExp of
         AppA {func, ...} =>
           if not (varIsD (VarAux.varVar func, d)) andalso isInDelta (delta, VarAux.varVar func)
             then [func]
             else []
       | CaseA {cases, default, ...} =>
         let
           val casesVarAuxs =
             case cases of
                Cases.Con v =>
                  unionVarAuxs
                    (Vector.toListMap (v, fn (_, exp) => innerVarAuxInDeltaExp delta d exp))
              | Cases.Word (_, v) =>
                  unionVarAuxs
                    (Vector.toListMap (v, fn (_, exp) => innerVarAuxInDeltaExp delta d exp))

           val defaultVarAuxs =
             case default of
                SOME exp => innerVarAuxInDeltaExp delta d exp
              | NONE => []
         in
           unionVarAuxs [casesVarAuxs, defaultVarAuxs]
         end
       | HandleA {try, handler, ...} =>
         let
           val tryVarAuxs = innerVarAuxInDeltaExp delta d try
           val handlerVarAuxs = innerVarAuxInDeltaExp delta d handler
         in
           unionVarAuxs [tryVarAuxs, handlerVarAuxs]
         end
       | LambdaA lambda => innerVarAuxInDeltaLambda delta d lambda
       | _  => []

    (* Annotates ExpAux *)
    fun handleExp (delta: Var.t list) (d: Def option) (ExpA {decs, result}) (indent: int) =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Annotating Exp with result ",
                            VarExp.layout result], indent))

      val decs = List.map (decs, handleDec delta d (indent + 2))

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "after annotation, decs annotated"], indent))
    in
      ExpA {decs = decs, result = result}
    end

    (* Annotates PrimExpAux *)
    and handlePrimExp delta d primExp indent =
      case primExp of
         AppA {func, arg} =>
         let
           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "Annotating App with func ",
                                 VarAux.layout func], indent))

           val func = newLsToVarAux (delta, d, func, indent + 2)

           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "after annotation: ",
                         VarAux.layout func], indent))
         in
           AppA {func = func, arg = arg}
         end
       | CaseA {test, cases, default} =>
         let
           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "Annotating Case with test ",
                         VarExp.layout test], indent))

           val cases =
             case cases of
                Cases.Con v =>
                  Cases.Con
                    (Vector.map (v, fn (pat, exp) => (pat, handleExp delta d exp (indent + 2))))
              | Cases.Word (ws, v) =>
                  Cases.Word
                    (ws,
                     Vector.map (v, fn (pat, exp) => (pat, handleExp delta d exp (indent + 2))))
            val default =
              case default of
                 SOME exp => SOME (handleExp delta d exp (indent + 2))
               | NONE => NONE
            
            val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "after annotation, cases and default annotated"], indent))
         in
           CaseA {test = test, cases = cases, default = default}
         end
       | ConAppA {con, targs, arg} =>
          let
            val conInfo = con
            val {con, lsArgs, ...} = ConInfo.dest conInfo

            val _ = debug (fn () =>
              Layout.indent (Layout.seq [Layout.str "Annotating constructor application of ",
                          Con.layout con], indent))

            val _ = if not (List.isEmpty lsArgs)
              then Error.bug "LambdaSetSpecialization.transform.annotateAux.handlePrimExp: unexpected con ls args"
              else ()

            val lsArgs = getLsArgsFromCon con
            val freshLsArgs = freshLsArgsFromTemplate lsArgs

            val _ = debug (fn () =>
              Layout.indent (Layout.seq [Layout.str "after con annotation, ls args: ",
                          List.layout Var.layout freshLsArgs], indent))
          in
            ConAppA {con = ConInfo.setLsArgs (conInfo, freshLsArgs),
                     targs = targs,
                     arg = arg}
          end
       | ConstA const => ConstA const
       | HandleA {try, catch, handler} =>
         let
           val (arg, ty) = catch
           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "Annotating Handle with arg ",
                                        Var.layout arg], indent))
           val try = handleExp delta d try (indent + 2)
           val handler = handleExp delta d handler (indent + 2)
           val _ = handleTy (arg, ty, (indent + 2))
           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "after annotation, try and handler annotated"], indent))
         in
           HandleA {try = try, catch = catch, handler = handler}
         end
       | LambdaA lambda => LambdaA (handleLambda delta d lambda (indent + 2)) (* TODO: We arent handling this as of now *)
       | PrimAppA {args, prim, targs} => PrimAppA {args = args, prim = prim, targs = targs}
       | ProfileA profile => ProfileA profile
       | RaiseA {exn, extend} => RaiseA {exn = exn, extend = extend}
       | SelectA {tuple, offset} => SelectA {tuple = tuple, offset = offset}
       | TupleA tuple => TupleA tuple
       | VarA var => VarA var

    (* Annotates DecAux *)
    and handleDec delta d indent dec =
      case dec of
         ExceptionA {arg, con} => ExceptionA {arg = arg, con = con}
       | FunA {decs, anns, tyvars, asLsArg, passedLsArgs, plist} =>
         let
           val _ = debug (fn () =>
              Layout.indent (Layout.seq [Layout.str "Annotating Fun with decs for vars ",
                                         List.layout Var.layout
                                                     (Vector.toListMap
                                                        (decs, fn {var: Var.t, ...} => var))],
                             indent))

           fun f ({lambda: LambdaAux.t, ty: Type.t, var: Var.t}) =
             {lambda = handleLambda delta d lambda (indent + 2),
              ty = handleTy (var, ty, (indent + 2)),
              var = var}

           val decs = Vector.map (decs, f)

           val vars = DecAux.funVars dec

           (* Get ls args for entire block. TODO: Use SCC for minimal *)
           val _ = if varIsD (List.first vars, d)
             then
               let
                 val indent = indent + 2

                 val _ = debug (fn () =>
                  Layout.indent (Layout.seq [Layout.str "Merging ls args for decs for vars ",
                                             List.layout Var.layout
                                                         (Vector.toListMap
                                                            (decs, fn {var: Var.t, ...} => var))],
                                 indent))
           
                 fun lsArgsOfBinding {ty, ...} =
                     TypeInfo.flatLsArgs (infoFromTy ty)

                 val innerVarAuxs =
                   unionVarAuxs (Vector.toListMap (decs,
                                                   fn {lambda, ...} =>
                                                     innerVarAuxInDeltaLambda delta d lambda))

                 val innerVarAuxsLsArgs =
                   List.map (innerVarAuxs,
                             fn var =>
                              case VarAux.passedLsArgs var of
                                 NONE => []
                               | SOME lsArg => lsArg)

                 val allLsLists = Vector.toList (Vector.map (decs, lsArgsOfBinding))

                 val mergedLs = unionLists (addUnique varNameEq) allLsLists
                 val mergedLs = unionLists (addUnique varNameEq) (mergedLs::innerVarAuxsLsArgs)
               in
                 setLsArgsFromDec (dec, mergedLs)
               end
             else ()

           val _ = debug (fn () =>
              Layout.indent (Layout.seq [(Layout.str "after annotation, decs for vars "),
                                         List.layout Var.layout
                                                     (Vector.toListMap
                                                        (decs, fn {var: Var.t, ...} => var))],
                             indent))
         in
           FunA {decs = decs,
                 anns = anns,
                 tyvars = tyvars,
                 asLsArg = asLsArg,
                 passedLsArgs = passedLsArgs,
                 plist = plist}
         end
       | MonoValA {exp, ty, var} =>
         let
           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "Annotating MonoVal with var ",
                                        Var.layout var], indent))

           val exp = handlePrimExp delta d exp (indent + 2)
           val ty = handleTy (var, ty, (indent + 2))

           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "after annotation, var and type annotated"], indent))
         in
           MonoValA {exp = exp, ty = ty, var = var}
         end
       | PolyValA _ =>
           Error.bug "LambdaSetSpecialization.transform.annotateAux.handleDec: unexpected PolyValA"

    (* Annotates LambdaAux *)
    and handleLambda delta d (LamA {arg, argType, body, mayInline, plist}) indent =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Annotating Lambda with arg ",
                    Var.layout arg], indent))
      val body = handleExp delta d body (indent + 2)
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "after annotation, body annotated"], indent))
    in
      LamA {arg = arg,
            argType = argType,
            body = body,
            mayInline = mayInline,
            plist = plist}
    end

    fun handleOneDef indent (def: Def, {aux: ExpAux.t, delta: Var.t list}): {aux: ExpAux.t, delta: Var.t list} =
    let
      val (decs, tyvars) =
        case def of
           DecAux.FunA {decs, tyvars, ...} => (decs, tyvars)
         | _ => Error.bug "LambdaSetSpecialization.transform.annotateAux.handleOneDef: expected FunA def"

      val _ = if not (isDef def)
        then Error.bug "LambdaSetSpecialization.transform.annotateAux.handleOneDef: expected def"
        else ()

      val _ = if not (Vector.isEmpty tyvars)
        then Error.bug "LambdaSetSpecialization.transform.annotateAux.handleOneDef: unexpected tyvars"
        else ()

      val _ = if not (1 = Vector.length decs)
        then Error.bug "LambdaSetSpecialization.transform.annotateAux.handleOneDef: expected exactly one dec in def"
        else ()

      val {ty, var, ...} = Vector.first decs

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Annotating def for var ",
                                   Var.layout var], indent))

      val _ = if isInDelta (delta, var)
        then Error.bug "LambdaSetSpecialization.transform.annotateAux.handleOneDef: unexpected def var in delta"
        else ()

      val aux = handleExp delta (SOME def) aux (indent + 2)
    in
      {aux = aux, delta = var :: delta}
    end

    val indent = 2

    val _ = debug (fn () => Layout.indent(Layout.str "annotateAux: starting", indent))

    val aux = handleExp [] NONE body indent
    val ret = List.fold (defs, {aux = aux, delta = []}, handleOneDef indent)

    val _ = debug (fn () => Layout.indent(Layout.str "annotateAux: finished", indent))
  in
    ret
  end


  (* Gathers our unification constraints, the `-^v^v->U` relation *)
  fun gatherConstraints (aux: ExpAux.t, delta: Var.t list):
      {aux: ExpAux.t, xi: (TypeInfo.t * TypeInfo.t) list} =
  let
    type xiType = (TypeInfo.t * TypeInfo.t) list
    type gammaTy = Var.t * int -> TypeInfo.t

    fun updateGammaWithInfo (gamma: gammaTy) (var: Var.t) (tyInfo: TypeInfo.t) (indent: int): gammaTy =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Updating gamma for var ",
                                   Var.layout var,
                                   Layout.str " with info ",
                                   TypeInfo.layout tyInfo], indent))
    in
      fn (v, indent) =>
        let
          val _ = debug (fn () =>
            Layout.indent (Layout.seq [Layout.str "Gamma v: ",
                                       Var.layout v,
                                       Layout.str ", var: ",
                                       Var.layout var,
                                       Layout.str ", found: ",
                                       Bool.layout (varNameEq (v, var))], indent))
        in
          if varNameEq (v, var) then tyInfo else gamma (v, indent)
        end
    end

    fun updateGamma (gamma: gammaTy) (var: Var.t) (ty: Type.t) (indent: int): gammaTy =
    let
      val eqCase = case getTyInfoFromVar var of
         SOME existingInfo => existingInfo
       | NONE => infoFromTy ty
    in
      updateGammaWithInfo gamma var eqCase indent
    end

    fun unionXis (xis: xiType list): xiType =
    let
      fun addUniqueXi (x: TypeInfo.t * TypeInfo.t, acc: xiType): xiType =
        if List.contains (acc, x,
                          fn ((x1, x2), (y1, y2)) =>
                            TypeInfo.equalsWithLsArgs (x1, y1) andalso
                            TypeInfo.equalsWithLsArgs (x2, y2))
          then acc
          else x :: acc
    in
      unionLists addUniqueXi xis
    end

    (* No need to recurse as tups are flat in SXML *)
    fun tiuTup
        (sigma: Var.t, gamma: gammaTy, res: Var.t, xs: VarExp.t vector, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = sigma (* TODO: do we need to check in xs? *)

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Tuple with components ",
                                   Vector.layout VarExp.layout xs], indent))

      val tyInfos = Vector.map (xs, fn varExp => gamma (VarExp.var varExp, indent + 2))
      val ty = TypeInfo.makeCon {tycon = Tycon.tuple, tyInfos = tyInfos}
      val resTy = gamma (res, indent + 2)
    in
      {xi = [(ty, resTy)], gamma = gamma, ty = ty}
    end


    (* No need to recurse again *)
    and tiuSelect (sigma: Var.t, gamma: gammaTy, res: Var.t, {tuple: VarExp.t, offset: int}, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = sigma (* Never used here but keep structure *)

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Select with tuple ",
                                   VarExp.layout tuple,
                                   Layout.str " and offset ", Int.layout offset], indent))

      val resTy = gamma (res, indent + 2)
      val tupleTyInfo = gamma (VarExp.var tuple, indent + 2)
      val tyAux: TypeAux.t = TypeInfo.ty tupleTyInfo
      val ty =
        case tyAux of
           TypeAux.ConA (tycon, tyInfos) =>
              if Tycon.equals (tycon, Tycon.tuple)
                then if offset < Vector.length tyInfos
                     then Vector.sub (tyInfos, offset)
                     else Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuSelect: select offset out of bounds"
                else Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuSelect: select on non-tuple type"
         | _ => Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuSelect: select on non-constructor type"
    in
      {xi = [(ty, resTy)], gamma = gamma, ty = ty}
    end

    (* and tiuInj *)
    and tiuCon (sigma: Var.t,
                gamma: gammaTy,
                res: Var.t,
                {con: ConInfo.t, arg: VarExp.t option, ...},
                indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val resTy = gamma (res, indent + 2)
      val {con=conI, ty, ...} = ConInfo.dest con

      val _ = sigma (* TODO: Do we need to check if in arg? *)

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Con case for con ",
                                   Con.layout conI,
                                   if Option.isSome arg
                                     then Layout.seq [Layout.str " with arg ",
                                                      VarExp.layout (Option.valOf arg)]
                                     else Layout.empty], indent))

      val tyInfo = case arg of
          SOME arg => gamma (VarExp.var arg, indent + 2)
        | NONE => TypeInfo.makeUnit ()

      val xi =
        case ty of
           SOME ty =>
             let
               val argTyInfo = infoFromTy ty
               val _ = debug (fn () =>
                 Layout.indent (Layout.seq [Layout.str "con has type, adding constraint between arg type info ",
                                            TypeInfo.layout argTyInfo,
                                            Layout.str " and expected type info from gamma ",
                                            TypeInfo.layout tyInfo], indent))
             in
               [(argTyInfo, tyInfo)]
             end
         | NONE =>
             let
               val _ = debug (fn () =>
                 Layout.indent (Layout.seq [Layout.str "con has no type, adding no constraint and returning gamma info for arg: ",
                                            TypeInfo.layout tyInfo], indent))
             in
               []
             end
      
      val tycon = getConTycon conI
      val conTyInfo = TypeInfo.makeCon {tycon = tycon, tyInfos = Vector.new0 ()}
    in
      {xi = (conTyInfo, resTy)::xi, gamma = gamma, ty = conTyInfo}
    end

    (* and tieFold *)

    (* and tiuUnfold *)

    and tiuMonoVal (sigma: Var.t,
                    gamma: gammaTy,
                    {exp: PrimExpAux.t, ty: Type.t, var: Var.t},
                    indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Gathering constraints from MonoVal for var ",
                                   Var.layout var], indent))

      val gammaP = updateGamma gamma var ty (indent + 2)
      val {xi, ty, ...} = handlePrimExp (sigma, gammaP, var, exp, (indent + 2))
    in
      (* Dec binidngs return updated gamma *)
      {xi = xi, gamma = gammaP, ty = ty}
    end

    and tiuCase (sigma: Var.t,
                gamma: gammaTy,
                ret: Var.t,
                {test: VarExp.t, cases: ExpAux.casesAux, default: ExpAux.t option},
                indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Case with test ",
                                   VarExp.layout test], indent))

      fun handleCaseCon ((pat: Pat.t, exp: ExpAux.t),
                         {xi: xiType, gamma: gammaTy, ty: TypeInfo.t})
          : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
      let
        val _ = debug (fn () =>
          Layout.indent (Layout.seq [Layout.str "Handling case with pattern ", Pat.layout pat],
                         indent + 2))

        val Pat.T {arg, con, ...} = pat

        val conTy = conToType con

        val (gammaP, argTy) = case arg of
           SOME (var, ty) => (updateGamma gamma var ty (indent + 2), SOME ty)
         | NONE => (gamma, NONE)

        val {xi=xiP, ty=tyP, ...} = handleExp (sigma, gammaP, ret, exp, (indent + 2))
        val xi = unionXis [xi, xiP]

        val xi =
          case (argTy, conTy) of
             (SOME argTy, SOME conTy) =>
               let
                 val argTyInfo = infoFromTy argTy
                 val conTyInfo = infoFromTy conTy
                 val _ = debug (fn () =>
                   Layout.indent (Layout.seq [Layout.str "Adding constraint between case pattern arg type info ",
                                              TypeInfo.layout argTyInfo,
                                              Layout.str " and con type info ",
                                              TypeInfo.layout conTyInfo], indent))
               in
                 (argTyInfo, conTyInfo) :: xi
               end
           | (NONE, NONE) => xi
           | _ =>
               Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuCase.handleCase: unexpected missing type in case pattern"
      in
        {xi = (ty, tyP)::xi, gamma = gamma, ty = ty}
      end

      fun handleCaseWord ((pat: WordX.t, exp: ExpAux.t),
                         {xi: xiType, gamma: gammaTy, ty: TypeInfo.t})
          : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
      let
        val _ = debug (fn () =>
          Layout.indent (Layout.seq [Layout.str "Handling case with pattern ",
                                     WordX.layout (pat, {suffix = true})],
                         indent + 2))

        val {xi=xiP, ty=tyP, ...} = handleExp (sigma, gamma, ret, exp, (indent + 2))
        val xi = List.append (xi, xiP)
      in
        {xi = (ty, tyP)::xi, gamma = gamma, ty = ty}
      end

      val retTy = gamma (ret, indent + 2)

      val xi = case default of
         SOME exp =>
           let
             val _ = debug (fn () =>
               Layout.indent (Layout.seq [Layout.str "Handling case default"], indent + 2))
              val {xi, ty = tyDef, ...} = handleExp (sigma, gamma, ret, exp, (indent + 2))
           in
              (retTy, tyDef)::xi
           end
       | NONE => []

      val {xi, ty, ...} =
        case cases of
           Cases.Con v =>
             let
               val {xi, ty, ...} = Vector.fold (v, {xi = xi, gamma = gamma, ty = retTy}, handleCaseCon)
             in
               {xi = xi, gamma = gamma, ty = ty}
             end
         | Cases.Word (_, v) =>
             let
               val {xi, ty, ...} = Vector.fold (v, {xi = xi, gamma = gamma, ty = retTy}, handleCaseWord)
             in
               {xi = xi, gamma = gamma, ty = ty}
             end
    in
      {xi = (ty, retTy)::xi, gamma = gamma, ty = ty}
    end

    and tiuApp (sigma: Var.t, gamma: gammaTy, res: Var.t, {func: VarAux.t, arg: VarExp.t}, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val var = VarAux.var func
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling App with func ",
                                   VarAux.layout func,
                                   Layout.str " and arg ",
                                   VarExp.layout arg], indent))
    in
      if isInDelta (delta, VarAux.varVar func)
        then tiuDefRule (sigma, gamma, func, indent + 2)
        else let
          val funcTyInfo = gamma (VarExp.var var, indent + 2)

          val funcTy = TypeInfo.ty funcTyInfo

          val (_, t2) =
            case funcTy of
               TypeAux.ConA (tycon, tyInfos) =>
                 if Tycon.equals (tycon, Tycon.arrow)
                   then case Vector.toList tyInfos of
                           [t1, t2] => (t1, t2)
                         | _ => Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuApp: expected exactly 2 type arguments for arrow type"
                   else Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuApp: expected arrow type for function in app"
             | _ => Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuApp: expected con type for function in app"

          val argTyInfo = gamma (VarExp.var arg, indent + 2)

          val newArrow = TypeInfo.makeCon {tycon = Tycon.arrow, tyInfos = Vector.fromList [argTyInfo, t2]}

          val resTy = gamma (res, indent + 2)
          val xi = [(funcTyInfo, newArrow), (resTy, t2)]
        in
          {xi = xi, gamma = gamma, ty = resTy}
        end
    end

    and tiuVar (sigma: Var.t, gamma: gammaTy, var: VarExp.t, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
      if isInDelta (delta, VarExp.var var)
        then Error.unimplemented "LambdaSetSpecialization.transform.gatherConstraints.tiuVar: handling variable in delta (recursive call)"
        else if varNameEq (VarExp.var var, sigma)
          then tiuSelfRef (sigma, gamma, VarAux.T {var = var, asLsArg = NONE, passedLsArgs = NONE}, indent + 2)
          else let
            val tyInfo = gamma (VarExp.var var, indent + 2)
          in
            {xi = [], gamma = gamma, ty = tyInfo}
          end

    and tiuDefRule (sigma: Var.t, gamma: gammaTy, def: VarAux.t, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val {var, passedLsArgs, ...} = VarAux.dest def

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling def rule for var ",
                                   VarAux.layout def,
                                   Layout.str " with sigma ",
                                   Var.layout sigma], indent))

      val ret = if varNameEq (VarExp.var var, sigma)
        then tiuSelfRef (sigma, gamma, def, indent + 2)
        else 
          let
            val varI = VarExp.var var

            val _ =
              if not (isInDelta (delta, varI))
                then Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuDefRule: expected def rule var to be in delta"
                else ()

            val dec = Option.valOf (getDecFromVar varI)
            val lsArgs = getLsArgsFromDec dec

            val typeInfo = gamma (varI, indent + 2)

            val passedLsArgs = case passedLsArgs of
               SOME args => args
             | NONE => []

            val _ = debug (fn () =>
              Layout.indent (Layout.seq [Layout.str "Def rule has ls args: ",
                                         List.layout Var.layout lsArgs,
                                         Layout.str " and passed ls args: ",
                                         List.layout Var.layout passedLsArgs], indent))

            val _ =
              if List.length passedLsArgs = List.length lsArgs
                then ()
                else Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuDefRule: length of passed ls args does not match expected"

            val mapOldToNew =
              if List.isEmpty lsArgs
                then fn var => var
                else
                  let
                    val oldNewPairs = List.zip (lsArgs, passedLsArgs)
                  in
                    fn var =>
                      case List.peek (oldNewPairs, (fn (old, _) => varNameEq (old, var))) of
                         SOME (_, new) => new
                       | NONE => var
                  end

            val tyInfoP = TypeInfo.mapLsArgs (typeInfo, mapOldToNew)
          in
            {xi = [], gamma = gamma, ty = tyInfoP}
          end
    in
      ret
    end

    and tiuSelfRef (sigma: Var.t, gamma: gammaTy, def: VarAux.t, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling self reference for var ",
                                   VarAux.layout def], indent))

      val _ = if not (varNameEq (sigma, VarAux.varVar def))
        then Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuSelfRef: expected self ref var to match sigma"
        else ()
      
      val tyInfo = getTyInfoFromVarAux def

      val _ = if Option.isNone tyInfo
        then Error.bug "LambdaSetSpecialization.transform.gatherConstraints.tiuSelfRef: expected type info for self ref var"
        else ()

      val tyInfo = Option.valOf tyInfo
    in
      {xi = [], gamma = gamma, ty = tyInfo}
    end

    and handleExp (sigma: Var.t, gamma: gammaTy, res: Var.t, exp: ExpAux.t, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Exp with result ",
                                   Var.layout res], indent))

      val res = VarExp.var (ExpAux.result exp)

      fun handleDecFun decs gamma indent =
      let
        val vars = Vector.map (decs, fn {var, ...} => var)

        val _ = debug (fn () =>
          Layout.indent (Layout.seq [Layout.str "Handling dec fun with vars ",
                                     List.layout Var.layout (Vector.toList vars)],
                         indent))

        fun handleOneInnerDec ({lambda: LambdaAux.t, var: Var.t, ...},
                               {xi: xiType, gamma: gammaTy})
            : {xi: xiType, gamma: gammaTy} =
        let
          val _ = debug (fn () =>
            Layout.indent (Layout.seq [Layout.str "Handling inner dec for var ",
                                       Var.layout var], indent))
          val sigma = if isInDelta (delta, var) then var else sigma (* Holds as Defs should only have one dec *)

          val tyInfo = Option.valOf (getTyInfoFromVar var)

          (* update for recursive calls in lambda body *)
          val gamma = updateGammaWithInfo gamma var tyInfo (indent + 2)
          
          val {xi=xiP, ...} = handleLambda (sigma, gamma, var, lambda, indent + 2)
          val xi = unionXis [xi, xiP]
        in
          {xi = xi, gamma = gamma}
        end

        val {xi=xiDecs, gamma=gammaDecs} =
          Vector.fold (decs, {xi = [], gamma = gamma}, handleOneInnerDec)
      in
        {xi = xiDecs, gamma = gammaDecs}
      end

      fun handleOneDec (dec: DecAux.t, {xi: xiType, gamma: gammaTy})
          : {xi: xiType, gamma: gammaTy} =
        case dec of
           DecAux.ExceptionA _ => {xi = xi, gamma = gamma} (* TODO *)
         | DecAux.FunA {decs, ...} =>
           let
             val {xi=xiP, gamma=gammaP, ...} = handleDecFun decs gamma indent
             val xi = unionXis [xi, xiP]
           in
             {xi = xi, gamma = gammaP}
           end
         | DecAux.MonoValA {exp, ty, var} =>
           let
             val {xi=xiP, gamma=gammaP, ...} =
               tiuMonoVal (sigma, gamma, {exp=exp, ty=ty, var=var}, indent)

             (* Sanity check that var info was updated in gamma *)
             val _ =
             let
               val res = gammaP (var, indent + 2)
               val expected = infoFromTy ty
               val _ = debug (fn () =>
                 Layout.indent (Layout.seq [Layout.str "Checking gamma updated for MonoVal var ",
                                            Var.layout var,
                                            Layout.str " expected info ",
                                            TypeInfo.layout expected,
                                            Layout.str " actual info ",
                                            TypeInfo.layout res], indent))
             in
               if TypeInfo.equals (res, expected)
                 then ()
                 else Error.bug "LambdaSetSpecialization.transform.gatherConstraints.handleExp: gamma not updated with MonoVal var type info"
             end

             val xi = unionXis [xi, xiP]
           in
             {xi = xi, gamma = gammaP}
           end
         | DecAux.PolyValA _ =>
              Error.bug "LambdaSetSpecialization.transform.gatherConstraints.handleExp: unexpected PolyValA in SXML"

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Exp decs"], indent))

      val {xi=xiDecs, gamma=gammaDecs, ...} =
        List.fold (ExpAux.decs exp, {xi = [], gamma = gamma}, handleOneDec)

      val resTy = Option.valOf (getTyInfoFromVar res)
      val resTyGamma = gammaDecs (res, indent + 2)
    in
      {xi = (resTy, resTyGamma)::xiDecs, gamma = gamma, ty = resTy}
    end

    and handlePrimExp (sigma: Var.t, gamma: gammaTy, res: Var.t, primExp: PrimExpAux.t, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling PrimExp for res ",
                                   Var.layout res], indent))

      val {xi, ty, ...} = case primExp of
         AppA app => tiuApp (sigma, gamma, res, app, indent + 2)
       | CaseA caseI => tiuCase (sigma, gamma, res, caseI, indent + 2)
       | ConAppA con => tiuCon (sigma, gamma, res, con, indent + 2)
       | ConstA _ => {xi = [], gamma = gamma, ty = TypeInfo.makeUnit ()}
       | HandleA handleI =>
         let
           val {try, catch=(arg, _), handler} = handleI

           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "Handling Handle with arg ",
                                        Var.layout arg], indent))

           val {xi=xiTry, ...} = handleExp (sigma, gamma, res, try, (indent + 2))

           val _ = debug (fn () =>
             Layout.indent (Layout.seq [Layout.str "after handling try part of Handle"], indent))

           val gammaP = updateGammaWithInfo gamma arg (Option.valOf (getTyInfoFromVar arg)) (indent + 2)

           val {xi=xiHandler, ...} = handleExp (sigma, gammaP, res, handler, (indent + 2))

           val xi = unionXis [xiTry, xiHandler]
         in
           {xi = xi, gamma = gamma, ty = gamma (res, indent + 2)} (* TODO ty *)
         end
       | LambdaA lambda => handleLambda (sigma, gamma, res, lambda, indent + 2)
       | PrimAppA _ => {xi = [], gamma = gamma, ty = TypeInfo.makeUnit ()} (* TODO *)
       | ProfileA _ => {xi = [], gamma = gamma, ty = TypeInfo.makeUnit ()} (* TODO *)
       | RaiseA _ => {xi = [], gamma = gamma, ty = TypeInfo.makeUnit ()} (* TODO *)
       | SelectA selectI => tiuSelect (sigma, gamma, res, selectI, indent + 2)
       | TupleA xs => tiuTup (sigma, gamma, res, xs, indent + 2)
       | VarA var => tiuVar (sigma, gamma, var, indent + 2)

      val resTy = gamma (res, indent + 2)
    in
      {xi = (ty, resTy)::xi, gamma = gamma, ty = resTy}
    end

    and handleLambda (sigma: Var.t, gamma: gammaTy, res: Var.t, lambda: LambdaAux.t, indent: int)
        : {xi: xiType, gamma: gammaTy, ty: TypeInfo.t} =
    let
      val {arg, argType, body, ...} = LambdaAux.dest lambda

      val _ = debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Handling Lambda ",
                                   Var.layout res,
                                   Layout.str " with arg ",
                                   Var.layout arg], indent))

      val argTyInfo = infoFromTy argType

      val _ =
        case getTyInfoFromVar arg of
          SOME existingInfo =>
            if TypeInfo.equals (existingInfo, argTyInfo)
              then ()
              else Error.bug "LambdaSetSpecialization.transform.gatherConstraints.handleLambda: conflicting type info for lambda arg var"
         | NONE => setTyInfoFromVar (arg, SOME argTyInfo)

      val gammaP = updateGammaWithInfo gamma arg argTyInfo (indent + 2)

      val {xi=xiBody, ty=tyBody, ...} = handleExp (sigma, gammaP, res, body, (indent + 2))

      val ty = TypeInfo.makeCon {tycon = Tycon.arrow, tyInfos = Vector.fromList [argTyInfo, tyBody]}

      val resTy = gamma (res, indent + 2)
      val xi = (ty, resTy)::xiBody
    in
      {xi = xi, gamma = gamma, ty = resTy}
    end

    val gammaDefault: gammaTy =
      fn (var, _) =>
        Error.bug
          (Layout.toString (Layout.seq
             [Layout.str "LambdaSetSpecialization.transform.gatherConstraints: out of scope var in gamma lookup - var: ", 
              Var.layout var]))

    val res = VarExp.var (ExpAux.result aux)
    val {xi, ...} = handleExp (Var.newString "BUG", gammaDefault, res, aux, 2)
  in
    {aux = aux, xi = xi}
  end

  fun dumpXi (xi: (TypeInfo.t * TypeInfo.t) list): unit =
    let
      fun layoutXi (x: TypeInfo.t * TypeInfo.t): Layout.t =
        let
          val (t1, t2) = x
        in
          Layout.seq [TypeInfo.layout t1,
                      Layout.str " ~ ",
                      TypeInfo.layout t2]
        end
    in
      debug (fn () =>
        Layout.indent (Layout.seq [Layout.str "Unification constraints:\n",
                                   List.layout layoutXi xi], 2))
    end


  (* First, annotate the explicit arrow types *)
  (* val _ = Vector.foreach (datatypes, annotateDatatype) *)

  (* Add the datatype dependencies to the graph *)
  val _ = Vector.foreach (datatypes, addDatatypeEdges)
  val _ = graphDump "pre elaboration"

  (* Look at each SCC for ls arg reqs *)
  val sccs = Graph.stronglyConnectedComponents g
  val _ = List.foreach (sccs, processDatatypeScc)
  val _ = graphDump "SCC init analysis"

  (* Propagate LS args bottom up *)
  val _ = propagateDatatypeLsArgs ()
  val _ = graphDump "Ls arg propagation"

  val _ = debug (fn () => Layout.str "Construct auxiliary exp for ls args")
  val {aux, defs, uoss} = expToAux body
  val _ = debug (fn () => Layout.str "Finished auxiliary exp for ls args")

  val _ = debug (fn () => Layout.str "Dumping auxiliary exp")
  val _ = debug (fn () => Layout.indent (ExpAux.layout aux, 2))
  val _ = debug (fn () => Layout.str "Finished dumping auxiliary exp")

  val _ = debug (fn () => Layout.str "Beginning auxiliary exp annotation, F")
  val {aux, delta} = annotateAux (aux, defs, uoss)
  val _ = debug (fn () => Layout.str "Finished auxiliary exp annotation, F")

  val _ = debug (fn () => Layout.str "Dumping auxiliary exp after F")
  val _ = debug (fn () => Layout.indent (ExpAux.layout aux, 2))
  val _ = debug (fn () => Layout.str "Finished dumping auxiliary exp")

  val _ = debug (fn () => Layout.str "Gather unification constraints")
  val {aux, xi} = gatherConstraints (aux, delta)
  val _ = debug (fn () => Layout.str "Finished gathering unification constraints")

  val _ = debug (fn () => Layout.str "Dumping xi")
  val _ = dumpXi xi
  val _ = debug (fn () => Layout.str "Finished dumping xi")

  val _ = debug (fn () => Layout.str "Destruct aux exp begin")
  val body = auxToExp aux
  val _ = debug (fn () => Layout.str "Finished aux exp destruct")

  val ret = Program.T { datatypes = datatypes, body = body }

  val _ = debug (fn () => Layout.str "Dumping Program")
  val _ = debug (fn () => Layout.indent (Program.layout ret, 2))
  val _ = debug (fn () => Layout.str "Finished dumping Program")
in
  ret
end

end
