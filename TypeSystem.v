Require Export VariableDefinitions.
Require Export Hlist.
Require Export Logic.

Module TypeSystem(E : Embedding).
Module APRHL := APRHL(E).

Import E.
Import APRHL.
Import APRHL.SEM.
Import APRHL.SEM.LAP.
Import APRHL.SEM.LAP.RP.
Import APRHL.SEM.LAP.RP.PP.
Import APRHL.SEM.LAP.RP.PP.MP.
Import APRHL.SEM.LAP.RP.PP.MP.UP.

Section Metrics.

  Record Metric (A : Type) := Build_metric
    {
      f :> A -> A -> option Z;
      f_nonneg : forall x y d, f x y = Some d -> (0 <= d)%Z;
      f_sym : forall x y, f x y = f y x;
      f_id : forall x, f x x = Some 0%Z;
    }.

  Lemma Metric_sym : forall {A : Type} (m : Metric A) (x y : A),
      m x y = m y x.
  Proof.
    apply f_sym.
  Qed.

  Lemma Metric_nonneg : forall {A : Type} (m : Metric A) (x y : A) d,
      m x y = Some d -> (0 <= d)%Z.
  Proof.
    apply f_nonneg.
  Qed.

  Lemma Metric_id : forall {A : Type} (m : Metric A) (x : A),
      m x x = Some 0%Z.
  Proof.
    apply f_id.
  Qed.

  Hint Resolve Metric_sym Metric_nonneg Metric_id.

  Arguments Build_metric [_] _ _ _ _.

  Definition bool_metric : Metric bool.
    refine (Build_metric (fun x y => if Bool.bool_dec x y then Some 0%Z else None) _ _ _).
    - intros x y d.
      destruct (Bool.bool_dec x y).
      + intros Heq; inversion Heq; omega.
      + intros contra; inversion contra.
    - intros x y; destruct (Bool.bool_dec x y); subst; auto.
      + destruct (Bool.bool_dec y y); auto. exfalso; apply n; auto.
      + destruct (Bool.bool_dec y x); auto. subst; exfalso; apply n; auto.
    - intros x. destruct (Bool.bool_dec x x); auto. exfalso; apply n; auto.
  Defined.

  Definition Z_metric : Metric Z.
    refine (Build_metric (fun x y => Some (Z.abs (x - y))) _ _ _).
    - intros x y d Heq.
      inversion Heq; subst; clear Heq; apply Z.abs_nonneg.
    - intros x y; f_equal.
      rewrite <- Z.abs_opp.
      rewrite Z.opp_sub_distr.
      rewrite Z.add_comm.
      reflexivity.
    - intros x.
      f_equal.
      rewrite Z.sub_diag.
      reflexivity.
  Defined.

  Fixpoint L1_metric_f {A : Type} (MA : Metric A) (l1 l2 : list A) : option Z :=
    match l1, l2 with
    | List.nil, List.nil => Some 0%Z
    | v1 :: l1, v2 :: l2 =>
      match MA v1 v2, L1_metric_f MA l1 l2 with
      | Some vd, Some vl => Some (vd + vl)%Z
      | _, _ => None
      end
    | _, _ => None
    end.

  Definition L1_metric : forall {A}, Metric A -> Metric (list A).
    intros A Metric_A.
    refine (Build_metric
              (L1_metric_f Metric_A) _ _ _).
    destruct Metric_A as [f_A f_nonneg_A f_sym_A f_id_A] eqn:HMA.
    - intros x y d.
      generalize dependent y.
      generalize dependent d.
      induction x.
      + intros d y; destruct y as [|v y].
        * simpl; intros Hd; inversion Hd; omega.
        * simpl; intros contra; inversion contra.
      + intros d y; destruct y as [|v y].
        * simpl; intros contra; inversion contra.
        * simpl. {
            destruct (f_A a v) eqn:H_v;
            destruct (L1_metric_f Metric_A x y) eqn:H_tail.
            - subst; rewrite H_tail; simpl; intros Hd; inversion Hd; subst.
              apply f_nonneg_A in H_v;
              apply IHx in H_tail;
              omega.
            - subst. rewrite H_tail. intros contra; inversion contra.
            - intros contra; inversion contra.
            - intros contra; inversion contra.
          }
    - intros x; induction x.
      + intros y; destruct y as [|v y].
        * reflexivity.
        * reflexivity.
      + intros y; destruct y as [|v y].
        * reflexivity.
        * simpl.
          rewrite IHx.
          rewrite Metric_sym.
          reflexivity.
    - induction x.
      + reflexivity.
      + simpl; rewrite Metric_id; rewrite IHx. reflexivity.
  Defined.

  Fixpoint remove_first
           {A : Type}
           (A_eqdec : forall (x y : A), {x = y} + {x <> y})
           (l : list A) (x : A) : list A :=
    match l with
    | List.nil => List.nil
    | y :: l => if A_eqdec y x then l else y :: (remove_first A_eqdec l x)
    end.

  Fixpoint bag_subtract
           {A : Type}
           (A_eqdec : forall (x y : A), {x = y} + {x <> y})
           (l1 l2: list A) :=
    match l2 with
    | List.nil => l1
    | (x :: l2) => bag_subtract A_eqdec (remove_first A_eqdec l1 x) l2
    end.

  Eval compute in bag_subtract Z.eq_dec [1; 2; 2; 3; 4; 5]%Z [2; 4; 8]%Z.
  Eval compute in bag_subtract Z.eq_dec [2; 4; 8]%Z [1; 2; 3; 4; 5]%Z.

  Definition bag_metric_f
             {A : Type}
             (A_eqdec : forall (x y : A), {x = y} + {x <> y})
             (l1 l2 : list A) :=
    Some (Z.of_nat (List.length (bag_subtract A_eqdec l1 l2)
                    + List.length (bag_subtract A_eqdec l2 l1))).

  Lemma bag_subtract_hd : forall A
                            (A_eqdec : forall (x y : A), {x = y} + {x <> y})
                            (a : A) (x y : list A),
      bag_subtract A_eqdec (a :: x) (a :: y) =
      bag_subtract A_eqdec x y.
  Proof.
    intros A A_eqdec a x y.
    simpl; destruct (A_eqdec a a).
    - reflexivity.
    - exfalso; apply n; auto.
  Qed.

  Lemma bag_metric_hd : forall A
                          (A_eqdec : forall (x y : A), {x = y} + {x <> y})
                          (a : A) (x y : list A),
      bag_metric_f A_eqdec (a :: x) (a :: y) =
      bag_metric_f A_eqdec x y.
  Proof.
    intros A A_eqdec.
    intros a x y.
    unfold bag_metric_f.
    f_equal. repeat rewrite bag_subtract_hd.
    reflexivity.
  Qed.

  Definition bag_metric : forall {A}, (forall (x y: A), {x = y} + {x <> y}) -> Metric (list A).
    intros A A_eqdec.
    refine (Build_metric (bag_metric_f A_eqdec) _ _ _).
    - intros x y d.
      intros Heq.
      unfold bag_metric_f in Heq.
      inversion Heq; subst; clear Heq.
      apply Zle_0_nat.
    - intros x y.
      unfold bag_metric_f.
      f_equal; f_equal.
      apply plus_comm.
    - induction x.
      + reflexivity.
      + rewrite bag_metric_hd; auto.
  Defined.

End Metrics.

Fixpoint tau_denote_metric (t : tau) : Metric (tau_denote t) :=
  match t with
  | t_int => Z_metric
  | t_bool => bool_metric
  | t_arr t => L1_metric (tau_denote_metric t)
  | t_bag t => bag_metric (tau_denote_eqdec t)
  end.

Definition dist_relation (t : tau) (v1 v2 : tau_denote t) (z : Z) : Prop :=
  exists d, tau_denote_metric t v1 v2 = Some d /\ (d <= z)%Z.

Definition tau_denote_dist (t : tau) := option Z.
Definition env := hlist tau tau_denote_dist.
Definition env_get {t ts} (x : var t ts) (e : env ts) := h_get e x.
Definition env_set {t ts} (x : var t ts) (e : env ts) (d : Z) := h_weak_update (Some d) e x.
Definition env_del {t ts} (x : var t ts) (e : env ts) := h_weak_update None e x.

Program Fixpoint denote_env {ts} (e : env ts) : memory_relation ts :=
  match e with
  | h_nil => fun _ _ => True
  | h_cons _ _ sd tl =>
    match sd with
    | None => denote_env tl
    | Some d => fun m1 m2 => denote_env tl m1 m2
    end
  end.

Next Obligation.

Module Test.
Example ts := [t_int; t_int; t_bool]%list.
Example x := m_first t_int [t_int; t_bool]%list.
Example y := m_next t_int (m_first t_int [t_bool]%list).
Example z := m_next t_int (m_next t_int (m_first t_bool []%list)).

Example env1 :=
  env_cons x 1 (env_cons y 2 (env_cons z 0 env_nil)).
Example env2 :=
  env_cons x 1 (env_cons y 2 (env_cons z 5 env_nil)).

Eval simpl in (denote_env env1).
Eval simpl in (denote_env env2).
Eval compute in (env_update env1 x 10).
End Test.

Definition liftM2_option {a b c} : (a -> b -> c) -> (option a -> option b -> option c) :=
  fun f o1 o2 => match o1, o2 with
              | Some o1, Some o2 => Some (f o1 o2)
              | _, _ => None
              end.

Definition liftM {a b} : (a -> b) -> (option a -> option b) :=
  fun f o => match o with
          | Some o => Some (f o)
          | _ => None
          end.

Definition comb_sens (s1 s2 : option Z) :=
  match s1, s2 with
  | Some s1, Some s2 =>
    if orb (s1 >? 0)%Z (s2 >? 0)%Z
    then None
    else Some 0%Z
  | _, _ => None
  end.

Fixpoint sens_expr {t : tau} {ts : list tau} (e : expr t ts) (ctx : @env ts) : option Z.
  destruct e eqn:He.
  - apply (Some 0%Z).
  - apply (env_get ctx v).
  - apply (liftM2_option Z.add (sens_expr _ _ e0_1 ctx) (sens_expr _ _ e0_2 ctx)).
  - apply (liftM2_option Z.add (sens_expr _ _ e0_1 ctx) (sens_expr _ _ e0_2 ctx)).
  - refine (match e0_1, e0_2 with
            | e_lit _ k, e2 => liftM (Z.mul k) (sens_expr _ _ e2 ctx)
            | e1, e_lit _ k => liftM (Z.mul k) (sens_expr _ _ e1 ctx)
            | e1, e2 => comb_sens (sens_expr _ _ e1 ctx) (sens_expr _ _ e2 ctx)
            end).
  - refine (match e0_1, e0_2 with
            | e1, e_lit _ k => liftM (fun z => Z.div z k) (sens_expr _ _ e1 ctx)
            | e1, e2 => comb_sens (sens_expr _ _ e1 ctx) (sens_expr _ _ e2 ctx)
            end).
  - pose (s1 := sens_expr _ _ e0_1 ctx).
    pose (s2 := sens_expr _ _ e0_2 ctx).
    apply (comb_sens s1 s2).
  - pose (s1 := sens_expr _ _ e0_1 ctx).
    pose (s2 := sens_expr _ _ e0_2 ctx).
    apply (comb_sens s1 s2).
  - pose (s1 := sens_expr _ _ e0_1 ctx).
    pose (s2 := sens_expr _ _ e0_2 ctx).
    apply (comb_sens s1 s2).
  - pose (s1 := sens_expr _ _ e0_1 ctx).
    pose (s2 := sens_expr _ _ e0_2 ctx).
    apply (comb_sens s1 s2).
Defined.

Lemma denote_env_var : forall {t ts} (m1 m2 : memory ts) (ctx : @env ts) (x : var t ts) v1 v2 d xd,
    denote_env ctx m1 m2 ->
    env_get ctx x = Some d ->
    mem_get m1 x = v1 ->
    mem_get m2 x = v2 ->
    tau_denote_metric t v1 v2 = Some xd ->
    (xd <= d)%Z.
Proof.
  intros t ts m1.
  generalize dependent t.
  dependent induction m1.
  - intros t m2 ctx x v1 v2 d xd Hsens Hd Hv1 Hv2.
    inversion x.
  - intros t m2 ctx y v1 v2 d xd Hsens Hd Hv1 Hv2 Hmetric.
    dependent destruction m2.
    dependent destruction ctx.
    + simpl in Hd; inversion Hd.
    + simpl in Hd.
      destruct (member_eq tau_eqdec v y).
      * admit.
      * dependent destruction ctx.
        apply IHm1 with (t := t) (m2 := m2) (ctx := ctx).


Lemma sens_expr_sound : forall {t ts} (m1 m2 : memory ts) (ctx : @env ts) (e : expr t ts) v1 v2 d vd,
    denote_env ctx m1 m2 ->
    sens_expr e ctx = Some d ->
    sem_expr m1 e = v1 ->
    sem_expr m2 e = v2 ->
    tau_denote_metric t v1 v2 = Some vd ->
    (vd <= d)%Z.
Proof.
  intros t ts m1 m2 ctx e.
  generalize dependent ctx.
  generalize dependent m2.
  generalize dependent m1.
  dependent induction e.
  - simpl. intros m1 m2 ctx v1 v2 d vd Hmem Hsens Hv1 Hv2 Hvd.
    inversion Hsens; subst; clear Hsens.
    rewrite <- Zminus_diag_reverse in Hvd.
    simpl in Hvd.
    inversion Hvd; omega.
  - simpl. intros m1 m2 ctx v1 v2 d vd Hmem Hsens Hv1 Hv2 Hvd.

Lemma assign_sound :
  forall {t ts} (ctx : @env ts) (x : var t ts) (e : expr t ts) d,
    sens_expr ctx e = d ->
    ([x <- e] ~_(0%R) [x <- e] : denote_env ctx ==> denote_env (env_update ctx x d))%triple.
(* Use aprhl_assign *)
Admitted.

End TypeSystem.
