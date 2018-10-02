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

  Definition val_bag_metric := bag_metric val_eqdec.

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

  Fixpoint val_metric_f (v1 v2 : val) {struct v1} : option Z :=
    match v1, v2 with
    | v_int z1, v_int z2 => Z_metric z1 z2
    | v_bool b1, v_bool b2 => bool_metric b1 b2
    | v_arr vs1, v_arr vs2 => val_arr_metric_f vs1 vs2
    | v_bag vs1, v_bag vs2 => val_bag_metric (val_arr_to_list vs1) (val_arr_to_list vs2)
    | _, _ => None
    end

  with

  val_arr_metric_f vs1 vs2 :=
    match vs1, vs2 with
    | v_nil, v_nil => Some 0%Z
    | v_cons v1 vs1, v_cons v2 vs2 =>
      lift_option2 Z.add (val_metric_f v1 v2) (val_arr_metric_f vs1 vs2)
    | _, _ => None
    end.

  Eval compute in (val_metric_f 1 2)%Z.
  Eval compute in (val_metric_f (v_arr (val_arr_from_list [v_int 1; v_int 2]%Z))
                                (v_arr (val_arr_from_list [v_int 2]%Z)))%list.
  Eval compute in (val_metric_f (v_arr (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                                (v_arr (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric_f (v_bag (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                                (v_bag (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric_f (v_bag (val_arr_from_list [v_int 1; v_int 2; v_int 3]%list))
                                (v_bag (val_arr_from_list [v_int 3; v_int 2; v_int 1]%list))).

  Definition val_metric : Metric val.
  Proof.
    refine (Build_metric val_metric_f _ _ _).
    {
      apply (val_ind_mut
               (fun x => forall y d, val_metric_f x y = Some d -> (0 <= d)%Z)
               (fun xvs => forall yvs d, (val_metric_f (v_arr xvs) (v_arr yvs) = Some d
                                  -> (0 <= d)%Z)
                                 /\ (val_metric_f (v_bag xvs) (v_bag yvs) = Some d
                                    -> (0 <= d)%Z)
               )
            ).
      - intros z y d Hd.
        destruct y; inversion Hd; subst; clear Hd.
        apply Z.abs_nonneg.
      - intros b y d Hd.
        destruct y; inversion Hd; subst; clear Hd.
        destruct (bool_dec b b0); inversion H0; subst; clear H0.
        omega.
      - intros xvs IH y d Hd.
        destruct y; inversion Hd as [Hd']; subst; clear Hd.
        destruct (IH v d) as [IHarr IHbag].
        simpl in IHarr; apply IHarr; auto.
      - intros xvs IH y d Hd.
        destruct y.
        + inversion Hd.
        + inversion Hd.
        + inversion Hd.
        + destruct (IH v d) as [IHarr IHbag].
          simpl in IHbag; apply IHbag; auto.
      - intros yvs d; simpl.
        split.
        + destruct yvs.
          intros H; inversion H; omega.
          intros contra; inversion contra.
        + destruct yvs; simpl.
          intros H; inversion H; subst; omega.
          intros H; inversion H; subst.
          apply Zle_0_nat.
      - intros v1 IH1 vs1 IH2 vs2 d.
        split.
        + intros Hd; destruct vs2 as [|v2 vs2]; inversion Hd as [Hd']; subst; clear Hd.
          destruct (val_metric_f v1 v2) eqn:Hv;
            destruct (val_arr_metric_f vs1 vs2) eqn:Hvs;
            inversion Hd' as [Hd'']; subst; clear Hd'.
          assert (0 <= z)%Z.
          { apply IH1 with (y := v2); auto. }
          assert (0 <= z0)%Z.
          { destruct (IH2 vs2 z0) as [IHarr IHbag]; apply IHarr; auto. }
          omega.
        + intros Hd; destruct vs2 as [|v2 vs2]; inversion Hd as [Hd']; subst; clear Hd.
          apply Pos2Z.is_nonneg.
          apply Zle_0_nat.
    }
    {
      apply (val_ind_mut
               (fun x => forall y, val_metric_f x y = val_metric_f y x)
               (fun xvs => forall yvs, (val_metric_f (v_arr xvs) (v_arr yvs) =
                                val_metric_f (v_arr yvs) (v_arr xvs))
                               /\ (val_metric_f (v_bag xvs) (v_bag yvs) =
                                  val_metric_f (v_bag yvs) (v_bag xvs)
                                 ))
            ).
      - intros z y; destruct y; auto.
        simpl. f_equal. rewrite <- Z.abs_opp.
        rewrite Z.opp_sub_distr.
        rewrite Z.add_comm.
        auto.
      - intros b y; destruct y; auto.
        simpl. destruct (bool_dec b b0); destruct (bool_dec b0 b); auto.
        exfalso; apply n; auto.
        subst. exfalso; apply n; auto.
      - intros xvs IH y.
        destruct y; auto.
        destruct (IH v) as [IHarr IHbag].
        apply IHarr; auto.
      - intros xvs IH y.
        destruct y; auto.
        destruct (IH v) as [IHarr IHbag].
        apply IHbag; auto.
      - intros yvs.
        destruct yvs; split; auto.
        simpl.
        unfold bag_metric_f.
        rewrite Nat.add_comm.
        auto.
      - intros v1 IH1 vs1 IH2 vs2; destruct vs2 as [|v2 vs2]; split; auto.
        + simpl; unfold bag_metric_f; rewrite Nat.add_comm; auto.
        + destruct (IH2 vs2) as [IHarr IHbag].
          simpl. simpl in IHarr. rewrite IHarr. rewrite IH1. auto.
        + simpl. unfold bag_metric_f. rewrite Nat.add_comm. auto.
    }
    {
      apply (val_ind_mut
               (fun x => val_metric_f x x = Some 0%Z)
               (fun xvs => (val_metric_f (v_arr xvs) (v_arr xvs) = Some 0%Z)
                        /\ (val_metric_f (v_bag xvs) (v_bag xvs) = Some 0%Z))

            ).
      - intros; simpl.
        rewrite Z.sub_diag; auto.
      - intros; simpl.
        destruct (bool_dec b b).
        auto.
        exfalso; apply n; auto.
      - intros vs IH.
        destruct IH as [IHarr IHbag]; auto.
      - intros vs IH.
        destruct IH as [IHarr IHbag]; auto.
      - auto.
      - intros v IH1 vs [IHarr IHbag]; split; auto.
        + simpl. rewrite IH1; simpl in IHarr; rewrite IHarr.
          reflexivity.
        + simpl. unfold bag_metric_f.
          simpl in IHbag.
          unfold bag_metric_f in IHbag.
          simpl.
          destruct (val_eqdec v v); auto.
          exfalso; apply n; auto.
    }
  Defined.

  Eval compute in (val_metric 1 2)%Z.
  Eval compute in (val_metric (v_arr (val_arr_from_list [v_int 1; v_int 2]%Z))
                              (v_arr (val_arr_from_list [v_int 2]%Z)))%list.
  Eval compute in (val_metric (v_arr (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                              (v_arr (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric (v_bag (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                              (v_bag (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric (v_bag (val_arr_from_list [v_int 1; v_int 2; v_int 3]%list))
                              (v_bag (val_arr_from_list [v_int 3; v_int 2; v_int 1]%list))).

End Metrics.

Definition env := VariableDefinitions.VarMap.t Z.
Definition env_get (x : var) (e : env) := VariableDefinitions.VarMap.find x e.
Definition env_set (x : var) (e : env) (d : Z) := VariableDefinitions.VarMap.add x d e.
Definition env_del (x : var) (e : env) := VariableDefinitions.VarMap.remove x e.

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
