Require Export ZArith.
Require Export Hlist.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.Structures.DecidableType.
Require Export Program.

Inductive tau :=
| t_int
| t_bool
| t_arr : tau -> tau
| t_bag : tau -> tau.

Fixpoint tau_denote (t : tau) : Set :=
  match t with
  | t_int => Z
  | t_bool => bool
  | t_arr t => list (tau_denote t)
  | t_bag t => list (tau_denote t)
  end.

Lemma tau_eqdec: forall (t t' : tau), {t = t'} + {t <> t'}.
Proof.
  intros t.
  induction t; destruct t';
  repeat match goal with
         | [ |- {t_int = t_int} + {?P} ] => left; auto
         | [ |- {t_int = ?X } + {t_int <> ?X}] => right; intros contra; inversion contra
         | [ |- {t_bool = t_bool} + {?P} ] => left; auto
         | [ |- {t_bool = ?X } + {t_bool <> ?X}] => right; intros contra; inversion contra
         | [ IH : forall t2, {?t1 = t2} + {?t1 <> t2 }
             |- {t_arr ?t1 = t_arr ?t2} + {t_arr ?t1 <> t_arr ?t2}] => idtac IH
         | [ |- {t_arr ?t1 = ?X} + {t_arr ?t1 <> ?X}] => right; intros contra; inversion contra
         | [ IH : forall t2, {?t1 = t2} + {?t1 <> t2 }
             |- {t_bag ?t1 = t_bag ?t2} + {t_bag ?t1 <> t_bag ?t2}] => idtac IH
         | [ |- {t_bag ?t1 = ?X} + {t_bag ?t1 <> ?X}] => right; intros contra; inversion contra
         end;
  (destruct (IHt t');
   [ left; f_equal; auto
   | right; intros contra; inversion contra; apply n; auto]).
Defined.

Fixpoint tau_denote_eqdec (t : tau) : forall (x y : tau_denote t), {x = y} + {x <> y} :=
  match t with
  | t_int => Z.eq_dec
  | t_bool => Bool.bool_dec
  | t_arr t => List.list_eq_dec (tau_denote_eqdec t)
  | t_bag t => List.list_eq_dec (tau_denote_eqdec t)
  end.

Definition tau_denote_eqb {t : tau} : tau_denote t -> tau_denote t -> bool :=
  fun x y => if tau_denote_eqdec t x y then true else false.

Inductive val :=
| v_int : Z -> val
| v_bool : bool -> val
| v_arr : list val -> val
| v_bag : list val -> val.

Lemma val_eqdec : forall v v' : val, {v = v'} + {v <> v'}.
Proof.
  (* Easy *)
Admitted.

Definition var := string.

Module StringDec <: DecidableType.
  Definition t := string.
  Definition eq : t -> t -> Prop := fun x y => x = y.
  Lemma eq_refl : forall x : t, x = x.
  Proof. auto. Qed.
  Lemma eq_sym : forall x y : t, x = y -> y = x.
  Proof. auto. Qed.
  Lemma eq_trans : forall x y z : t, x = y -> y = z -> x = z.
  Proof. intros x y z H; rewrite H; auto. Qed.
  Definition eq_dec := string_dec.
End StringDec.