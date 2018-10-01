Require Export ZArith.
Require Export Hlist.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Coq.Structures.DecidableType.
Require Export Program.
Require Export FMapWeakList.
Require Export Coq.FSets.FMapInterface.

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

Section Val_Rect.

  Variable P : val -> Type.
  Variable P_arr : list val -> Type.
  Variable P_bag : list val -> Type.

  Hypothesis int_case : forall z, P (v_int z).
  Hypothesis bool_case : forall b, P (v_bool b).

  Hypothesis arr_val : forall vs, P_arr vs -> P (v_arr vs).
  Hypothesis arr_nil : P_arr [].
  Hypothesis arr_case : forall v vs, P v -> P_arr vs -> P_arr (v :: vs).

  Hypothesis bag_val : forall vs, P_bag vs -> P (v_bag vs).
  Hypothesis bag_nil : P_bag [].
  Hypothesis bag_case : forall v vs, P v -> P_bag vs -> P_bag (v :: vs).

  Fixpoint val_rect1 (v : val) : P v :=
    match v with
    | v_int z => int_case z
    | v_bool b => bool_case b
    | v_arr vs => arr_val vs
                         ((list_rect
                             P_arr
                             arr_nil
                             (fun v vs Pvs => arr_case v vs (val_rect1 v) Pvs))
                            vs)
    | v_bag vs => bag_val vs
                         (list_rect
                            P_bag
                            bag_nil
                            (fun v vs Pvs => bag_case v vs (val_rect1 v) Pvs)
                         vs)
    end.

End Val_Rect.

Section Val_Ind.

  Variable P : val -> Prop.
  Hypothesis z_case : forall z, P (v_int z).
  Hypothesis b_case : forall b, P (v_bool b).
  Hypothesis arr_case : forall ls, Forall P ls -> P (v_arr ls).
  Hypothesis bag_case : forall ls, Forall P ls -> P (v_bag ls).

  Definition val_ind1 (v : val) : P v :=
    val_rect1
      P (Forall P) (Forall P)
      z_case b_case
      arr_case
      (Forall_nil P)
      (fun v vs pv pvs => Forall_cons v pv pvs)
      bag_case
      (Forall_nil P)
      (fun v vs pv pvs => Forall_cons v pv pvs)
      v.
End Val_Ind.

Coercion v_int : Z >-> val.
Coercion v_bool : bool >-> val.

Lemma val_eqdec : forall v v' : val, {v = v'} + {v <> v'}.
Proof.
  (* Use hand written induction principle *)
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

Module VarMap := Make(StringDec).

Lemma VarMap_Equal_dec : forall {T}
                           (H: forall x1 x2: T, {x1 = x2} + {x1 <> x2})
                           (m1 m2: VarMap.t T),
    {VarMap.Equal m1 m2} + {~(VarMap.Equal m1 m2)}.
Proof.
  intros T Heq_dec m1 m2.
  (* Not easy to prove, we might need to use Arthur's extensional data structure library *)
Admitted.

Lemma VarMap_Equal_Refl : forall {T} (m : VarMap.t T),
    VarMap.Equal m m.
Proof.
  intros T m.
  unfold VarMap.Equal.
  reflexivity.
Qed.

Lemma VarMap_Equal_Sym : forall {T} (m1 m2 : VarMap.t T),
    VarMap.Equal m1 m2 -> VarMap.Equal m2 m1.
Proof.
  intros T m1 m2.
  unfold VarMap.Equal.
  auto.
Qed.

Lemma VarMap_Equal_Trans : forall {T} (m1 m2 m3 : VarMap.t T),
    VarMap.Equal m1 m2 -> VarMap.Equal m2 m3 -> VarMap.Equal m1 m3.
Proof.
  intros T m1 m2 m3.
  unfold VarMap.Equal.
  intros H1 H2.
  intros y.
  rewrite H1.
  auto.
Qed.

Add Parametric Relation T : (VarMap.t T) (@VarMap.Equal T)
    reflexivity proved by VarMap_Equal_Refl
    symmetry proved by VarMap_Equal_Sym
    transitivity proved by VarMap_Equal_Trans
      as VarMap_Equal_Equiv.
