Require Export ZArith.
Require Export Coq.Lists.List.
Require Export Coq.Strings.String.
Require Export Program.
Require Export FMapWeakList.
Require Export FSetWeakList.
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

Fixpoint val_arr_update_nat (vs: val_arr) (idx: nat) (v: val) : option val_arr :=
  match vs, idx with
  | v_nil, _ => None
  | v_cons _ vs, O => Some (v_cons v vs)
  | v_cons v vs, S n =>
    match val_arr_update_nat vs n v with
    | None => None
    | Some vs' => Some (v_cons v vs')
    end
  end.

Fixpoint val_arr_subarr_nat (vs: val_arr) (len: nat) : option val_arr :=
  match vs, len with
  | _, O => Some v_nil
  | v_cons v vs, S n =>
    match val_arr_subarr_nat vs n with
    | Some vs' => Some (v_cons v vs')
    | None => None
    end
  | v_nil, S _ => None
  end.

Fixpoint val_arr_subarr (vs: val_arr) (len: Z) : option val_arr :=
  match len with
  | Z0 => val_arr_subarr_nat vs O
  | Zpos p => val_arr_subarr_nat vs (Pos.to_nat p)
  | Zneg _ => None
  end.

Fixpoint val_arr_to_list (vs : val_arr) : list val :=
  match vs with
  | v_nil => []
  | v_cons v vs => v :: val_arr_to_list vs
  end.

Fixpoint val_arr_from_list (vs : list val) : val_arr :=
  match vs with
  | [] => v_nil
  | v :: vs => v_cons v (val_arr_from_list vs)
  end.

Fixpoint val_arr_update (vs: val_arr) (idx: Z) (v: val) : option val_arr :=
  match idx with
  | Z0 => val_arr_update_nat vs O v
  | Zpos idx => val_arr_update_nat vs (Pos.to_nat idx) v
  | Zneg _ => None
  end.

Fixpoint val_arr_update_length_nat (t : tau) (vs: val_arr) (len: nat): val_arr :=
  match vs, len with
  | _, O => v_nil
  | v_cons v vs, S n =>
    v_cons v (val_arr_update_length_nat t vs n)
  | v_nil, n =>
    val_arr_from_list (repeat (tau_default_val t) n)
  end.

Definition val_arr_update_length (t : tau) (vs : val_arr) (len: Z): option val_arr :=
  match len with
  | Z0 => Some (val_arr_update_length_nat t vs O)
  | Zpos len => Some (val_arr_update_length_nat t vs (Pos.to_nat len))
  | Zneg _ => None
  end.

Fixpoint val_arr_map (f: val -> val) (vs: val_arr) :=
  match vs with
  | v_nil => v_nil
  | v_cons x xs => v_cons (f x) (val_arr_map f xs)
  end.

Fixpoint val_arr_map_option (f: val -> option val) (vs: val_arr) :=
  match vs with
  | v_nil => Some v_nil
  | v_cons x xs =>
    match f x, val_arr_map_option f xs with
    | Some v, Some vs => Some (v_cons v vs)
    | _, _ => None
    end
  end.

Lemma val_arr_length_positive: forall vs len,
    val_arr_length vs = len
    -> (0 <= len)%Z.
Proof.
  intros vs len Hlen.
  unfold val_arr_length in Hlen.
  rewrite <- Hlen.
  omega.
Qed.

Lemma val_arr_update_length_pos: forall t vs len,
    (0 <= len)%Z
    -> exists vs', val_arr_update_length t vs len = Some vs'.
Proof.
  intros t vs len Hlen_pos.
  assert (Z0 = len \/ exists len_pos, Zpos len_pos = len).
  {
    destruct len eqn:Hlen.
    left; auto.
    right. exists p; auto.
    exfalso. apply Hlen_pos. auto.
  }
  destruct H.
  - subst. exists v_nil.
    destruct vs; auto.
  - destruct H as [len_pos Hlen_pos2].
    unfold val_arr_update_length.
    exists (val_arr_update_length_nat t vs (Pos.to_nat len_pos)).
    subst.
    auto.
Qed.

Lemma val_arr_length_from_list:
  forall l, val_arr_length_nat (val_arr_from_list l) = List.length l.
Proof.
  induction l.
  - reflexivity.
  - simpl. rewrite IHl; auto.
Qed.

Lemma val_arr_update_length_nat_correct: forall t vs vs' len,
    val_arr_update_length_nat t vs len = vs'
    -> val_arr_length_nat vs' = len.
Proof.
  intros t vs vs' len Hlen.
  generalize dependent len.
  generalize dependent vs'.
  induction vs.
  - intros vs' len Hlen.
    simpl in Hlen.
    destruct len.
    + subst. auto.
    + subst. rewrite val_arr_length_from_list.
      simpl. f_equal.
      rewrite repeat_length.
      auto.
  - intros vs' len Hlen.
    simpl in Hlen.
    destruct len.
    + subst. auto.
    + subst. simpl.
      f_equal.
      remember (val_arr_update_length_nat t vs len) as vs'.
      apply IHvs; auto.
Qed.

Lemma val_arr_update_length_correct: forall t vs vs' len,
    val_arr_update_length t vs len = Some vs'
    -> val_arr_length vs' = len.
Proof.
  intros t vs vs' len Hlen.
  unfold val_arr_update_length in Hlen.
  unfold val_arr_length.
  destruct len.
  - inversion Hlen. erewrite val_arr_update_length_nat_correct; eauto.
    reflexivity.
  - inversion Hlen. erewrite val_arr_update_length_nat_correct; eauto.
    rewrite positive_nat_Z; auto.
  - inversion Hlen.
Qed.

Hint Resolve val_arr_length_positive.
Hint Resolve val_arr_update_length_pos.
Hint Resolve val_arr_update_length_correct.

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

Module VarMap := FMapWeakList.Make(StringDec).
Module VarSet := FSetWeakList.Make(StringDec).

Definition VarMap_includes_compute
           {T} (eq: T -> T -> bool) (m1 m2:VarMap.t T) :=
  VarMap.fold (fun x v is_equal =>
                 match VarMap.find x m2 with
                 | Some v2 => is_equal && (eq v v2)
                 | _ => false
                 end
              ) m1 true.

Definition varmap_from_list {A: Type} (xs: list (var * A)%type) : VarMap.t A :=
  List.fold_right (fun xa m => VarMap.add (fst xa) (snd xa) m) (@VarMap.empty A) xs.

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

Definition str_to_var : string -> var := fun x => x.
Coercion str_to_var : string >-> var.

Lemma VarMap_MapsTo_Uniq: forall {T} m x (v1 v2 : T),
    VarMap.MapsTo x v1 m -> VarMap.MapsTo x v2 m
    -> v1 = v2.
Proof.
  intros T m x v1 v2.
  intros Hv1.
  intros Hv2.
  apply VarMap.find_1 in Hv1.
  apply VarMap.find_1 in Hv2.
  rewrite Hv1 in Hv2.
  inversion Hv2; subst; auto.
Qed.

Lemma VarMap_MapsTo_remove_False: forall {T} m x (v:T),
    ~(VarMap.MapsTo x v (VarMap.remove x m)).
Proof.
  intros T m x v Hxv.
  assert (H_not_In: ~VarMap.In x (VarMap.remove x m)).
  { apply VarMap.remove_1; auto. }
  unfold VarMap.MapsTo in *. unfold VarMap.In in *.
  unfold VarMap.Raw.PX.MapsTo in *.
  unfold VarMap.Raw.PX.In in *.
  apply H_not_In.
  exists v; auto.
Qed.

Lemma VarMap_remove_same: forall {T} (m : VarMap.t T) x,
    VarMap.find x m = None
    -> VarMap.Equal (VarMap.remove x m) m.
Proof.
  intros T m x Hfind.
  unfold VarMap.Equal.
  intros y.
  destruct (StringDec.eq_dec x y).
  - subst. rewrite Hfind.
    assert (forall v, ~(VarMap.MapsTo y v (VarMap.remove y m))).
    { apply VarMap_MapsTo_remove_False; auto. }
    destruct (VarMap.find y (VarMap.remove y m)) eqn:Hy; auto.
    apply VarMap.find_2 in Hy.
    apply H in Hy. inversion Hy.
  - destruct (VarMap.find y m) eqn:Hy.
    * apply VarMap.find_2 in Hy.
      apply VarMap.find_1.
      apply VarMap.remove_2; auto.
    * destruct (VarMap.find y (VarMap.remove x m)) eqn:Hyx; auto.
      apply VarMap.find_2 in Hyx.
      apply VarMap.remove_3 in Hyx.
      apply VarMap.find_1 in Hyx.
      rewrite Hyx in Hy.
      auto.
Qed.

Lemma VarMap_remove_None: forall {T} (m: VarMap.t T) x,
    VarMap.find x m = None
    -> VarMap.find x (VarMap.remove x m) = None.
Proof.
  intros T m x Hfind.
  rewrite VarMap_remove_same; auto.
Qed.

Hint Resolve VarMap_MapsTo_Uniq.
