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

Definition var (t: tau) (ts: list tau) := @member tau t ts.