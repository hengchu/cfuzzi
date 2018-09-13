Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Structures.DecidableType.
Require Export Syntax.

Module VarDec <: DecidableType.
  Definition t := var.
  Definition eq (v1 v2 : t) := (v1 = v2).
  Lemma eq_refl : forall x : t, eq x x.
  Proof.
    reflexivity.
  Qed.

  Lemma eq_sym : forall x y : t, eq x y -> eq y x.
  Proof.
    intros.
    rewrite H; reflexivity.
  Qed.

  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros.
    rewrite H.
    rewrite H0.
    reflexivity.
  Qed.

  Definition eq_dec := string_dec.
End VarDec.

Import VarDec.
Module VarMap := FMapWeakList.Make(VarDec).

Open Scope string_scope.

Check (VarMap.empty).
Eval compute in (VarMap.add "x" (v_int 1%Z) (@VarMap.empty val)).
Eval compute in (VarMap.find "x" (VarMap.add "x" (v_int 1%Z) (@VarMap.empty val))).
Eval compute in (VarMap.find "y" (VarMap.add "x" (v_int 1%Z) (@VarMap.empty val))).