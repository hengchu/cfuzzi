Require Export ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
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
| v_arr : tau -> val_arr -> val
| v_bag : tau -> val_arr -> val
with
val_arr :=
| v_nil : val_arr
| v_cons : val -> val_arr -> val_arr.

Scheme val_ind_mut := Induction for val Sort Type
  with val_arr_ind_mut := Induction for val_arr Sort Type.

Lemma val_eqdec: forall v v' : val, {v = v'} + {v <> v'}.
Proof.
  apply (val_ind_mut
           (fun v => forall v', {v = v'} + {v <> v'})
           (fun vs => forall vs', {vs = vs'} + {vs <> vs'})
        ).
  - intros z; destruct v'; auto.
    + destruct (Z.eq_dec z z0); subst; auto.
      right; intros contra; inversion contra; subst; apply n; auto.
    + right; intros contra; inversion contra.
    + right; intros contra; inversion contra.
    + right; intros contra; inversion contra.
  - intros b; destruct v'; auto.
    + right; intros contra; inversion contra.
    + destruct (bool_dec b b0); subst; auto.
      right; intros contra; inversion contra; subst; exfalso; apply n; auto.
    + right; intros contra; inversion contra.
    + right; intros contra; inversion contra.
  - intros t vs IH; destruct v'; auto.
    + right; intros contra; inversion contra.
    + right; intros contra; inversion contra.
    + destruct (IH v); destruct (tau_eqdec t t0); subst; auto.
      * right; intros contra; inversion contra; subst; exfalso; apply n; auto.
      * right; intros contra; inversion contra; subst; exfalso; apply n; auto.
      * right; intros contra; inversion contra; subst; exfalso; apply n; auto.
    + right; intros contra; inversion contra.
  - intros t vs IH; destruct v'; auto.
    + right; intros contra; inversion contra.
    + right; intros contra; inversion contra.
    + right; intros contra; inversion contra.
    + destruct (IH v); destruct (tau_eqdec t t0); subst; auto.
      * right; intros contra; inversion contra; subst; exfalso; apply n; auto.
      * right; intros contra; inversion contra; subst; exfalso; apply n; auto.
      * right; intros contra; inversion contra; subst; exfalso; apply n; auto.
  - intros vs'; destruct vs'; auto.
    right; intros contra; inversion contra.
  - intros v1 IH1 vs1 IH2 vs2.
    destruct vs2; auto.
    + right; intros contra; inversion contra.
    + destruct (IH1 v); destruct (IH2 vs2); subst; auto.
      * right; intros contra; inversion contra; subst; apply n; auto.
      * right; intros contra; inversion contra; subst; apply n; auto.
      * right; intros contra; inversion contra; subst; apply n; auto.
Defined.

Definition tau_default_val (t : tau) :=
  match t with
  | t_int => v_int 0%Z
  | t_bool => v_bool false
  | t_arr t => v_arr t v_nil
  | t_bag t => v_bag t v_nil
  end.

Search (Z -> nat).

Fixpoint val_arr_index_nat (vs : val_arr) (idx : nat) : option val :=
  match vs, idx with
  | v_nil, _ => None
  | v_cons v _, O => Some v
  | v_cons v vs, S n' => val_arr_index_nat vs n'
  end.

Definition val_arr_index (vs : val_arr) (idx : Z) :=
  match idx with
  | Z0 => val_arr_index_nat vs O
  | Zpos p => val_arr_index_nat vs (Pos.to_nat p)
  | Zneg _ => None
  end.

Fixpoint val_arr_length_nat (vs : val_arr) : nat :=
  match vs with
  | v_nil => O
  | v_cons v vs => S (val_arr_length_nat vs)
  end.

Definition val_arr_length (vs : val_arr) := Z.of_nat (val_arr_length_nat vs).

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

Definition var_eqdec := StringDec.eq_dec.

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


Coercion v_int : Z >-> val.
Coercion v_bool : bool >-> val.
