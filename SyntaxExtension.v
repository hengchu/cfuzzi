Require Export TypeSystem.

Fixpoint uncurry_P (premises : list Prop) (conclusion : Prop) :=
  match premises with
  | []%list => conclusion
  | (p :: ps)%list => p -> (uncurry_P ps conclusion)
  end.

Module Type Extension (E: Embedding).

Module APRHL := APRHL(E).
Module TS := TypeSystem.TypeSystem(E).

Import APRHL.
Import TS.

(* The extra syntax we are adding *)
Parameter syntax : list tau -> Type.

(* How to compile the new syntax into orignal language *)
Parameter compile : forall {ts}, syntax ts -> cmd ts.

(* Coercion into lists of instructions so we can mix syntax freely *)
Coercion compile : syntax >-> list.

(* The premises of the typing rule can range over pre-condition, syntax, post
   condition and epsilon *)
Parameter premises : forall ts (pre : @env ts) (c : syntax ts) (post : @env ts) (eps : R), list Prop.

(* The proof of the typing rule for this extension *)
Parameter typing_rule:
  forall ts (pre : @env ts) (c : syntax ts) (post : @env ts) (eps : R),
      let c' := compile c in
      uncurry_P
        (premises ts pre c post eps)
        (c' ~_(eps) c' : denote_env pre ==> denote_env post)%triple.

End Extension.
