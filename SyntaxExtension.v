Require Export TypeSystem.

Fixpoint uncurry_P (premises : list Prop) (conclusion : Prop) :=
  match premises with
  | []%list => conclusion
  | (p :: ps)%list => p -> (uncurry_P ps conclusion)
  end.

Module Type Extension (E: Embedding).

Module TS := TypeSystem.TypeSystem(E).

Import TS.
Import TS.APRHL.

(* The extra syntax we are adding *)
Parameter syntax : Type.

(* How to compile the new syntax into orignal language *)
Parameter compile : syntax -> cmd.

(* Coercion into lists of instructions so we can mix syntax freely *)
Coercion compile : syntax >-> cmd.

(* The premises for ensuring this syntax extension is welltyped in the base language *)
Parameter premises_type : forall (tctx : st_env) (c : syntax), list Prop.

(* A proof of the welltyped-property, using the premises above *)
Parameter typing_rule_type:
  forall (tctx : st_env) (c : syntax),
    let c' := compile c in
    uncurry_P (premises_type tctx c) (welltyped tctx c').

(* The premises of the typing rule can range over pre-condition, syntax, post
   condition and epsilon *)
Parameter premises_sens : forall (tctx : st_env) (pre : env) (c : syntax) (post : env) (eps : R), list Prop.

(* The proof of the typing rule for this extension *)
Parameter typing_rule_sens:
  forall (tctx : st_env) (pre : env) (c : syntax) (post : env) (eps : R),
      let c' := compile c in
      uncurry_P
        (premises_sens tctx pre c post eps)
        (c' ~_(eps) c' : denote_env pre ==> denote_env post)%triple.

End Extension.
