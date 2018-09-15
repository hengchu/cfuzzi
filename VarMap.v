Require Import Coq.FSets.FMapWeakList.
Require Import Coq.Structures.DecidableType.
Require Export VariableDefinitions.

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

Module VarMap := FMapWeakList.Make(VarDec).
Export VarMap.

Lemma Equiv_trans : forall {A} m1 m2 m3 R,
    @Equiv A R m1 m2 -> @Equiv A R m2 m3 -> @Equiv A R m1 m3.
Admitted.
