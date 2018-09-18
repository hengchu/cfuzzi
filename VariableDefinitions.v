Require Export ZArith.
Require Export Hlist.

Inductive tau :=
| t_int
| t_bool.

Definition tau_denote (t : tau) : Set :=
  match t with
  | t_int => Z
  | t_bool => bool
  end.

Definition tau_eqb (t : tau) : tau_denote t -> tau_denote t -> bool :=
  match t with
  | t_int => Z.eqb
  | t_bool => Bool.eqb
  end.

Lemma tau_eqdec: forall (t t' : tau), {t = t'} + {t <> t'}.
Proof.
  intros t t'.
  destruct t; destruct t'; auto.
  - right; intros contra; inversion contra.
  - right; intros contra; inversion contra.
Defined.

Definition var (t: tau) (ts: list tau) := @member tau t ts.
