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


fun transform (Program.T {datatypes, body, ...}): Program.t =
  let
    (*
    fun loopExp (e: Exp.t): unit =
      let
        val {decs, ...} = Exp.dest e
        val _ = print "Debug exp\n"
      in
        List.foreach (decs, loopDec)
      end

    and loopDec (d: Dec.t): unit =
      case d of
         MonoVal {exp, ...}  => loopPrimExp exp
       | PolyVal {exp, ...} => loopExp exp
       | Exception _ => ()
       | Fun {anns, decs, ...} =>
           let
             val _ = Vector.foreach (decs, fn {lambda, ...} => loopLambda lambda)
             val _ = print "Debug dec\n"
           in
             (case anns of
                 NONE => ()
               | SOME _ => Vector.foreach (decs, fn {var, ...} =>
                     print ((Var.toString var) ^ "\n")))
            end

    and loopPrimExp (e: PrimExp.t): unit =
      case e of
       | PrimExp.Lambda l => loopLambda l
       | PrimExp.Handle {try, handler, ...} =>
           (loopExp try; loopExp handler)
       | PrimExp.Case {cases, default, ...} =>
           (Cases.foreach (cases, loopExp)
            ; Option.app (default, loopExp))
       | _ => ()

    and loopLambda (l: Lambda.t): unit =
      let
        val {body, ...} = Lambda.dest l
      in
        loopExp body
      end
    *)

    val newTypeVar = Var.newString "a_"

    fun containsArrow t = Type.containsTycon (t, Tycon.arrow)

    fun annotateDatatypes datatypes =
    let
      val d : (Tycon.t, {lsv: Var.t, con: {arg: Type.t option, con: Con.t}} vector) HashTable.t =
        HashTable.new {hash = Tycon.hash, equals = Tycon.equals}

      fun getArrowCons (cons: {arg: Type.t option, con: Con.t} vector) =
        Vector.fromList
          (Vector.foldr (cons, [],
                         fn ({arg, con}, xs) => (* refactor to be less confusing *)
                           case arg of
                              SOME ty => if containsArrow ty then
                                ({arg=arg, con=con} :: xs) else xs
                            | _ => xs))
      
      fun f ({cons, tycon, ...}) = (* TODO: Handle tyvars *)
      let
        val arrowCons = getArrowCons (cons)

        (* TODO: Check logic as we have our lsv and our con in one record *)
        val annotArrowCons = Vector.map (arrowCons, fn con => {lsv = newTypeVar, con = con}) 
      in
        ignore (HashTable.lookupOrInsert (d, tycon, fn () => annotArrowCons))
      end

      val _ = Vector.map (datatypes, f)
    in
      d
    end

    val d = annotateDatatypes datatypes


  in
    Program.T {datatypes = datatypes, body = body}
  end

end
