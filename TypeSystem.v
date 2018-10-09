Require Export Cfuzzi.VariableDefinitions.
Require Export Cfuzzi.Logic.
Require Export Cfuzzi.Semantics.

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
    | v_arr _ vs1, v_arr _ vs2 => val_arr_metric_f vs1 vs2
    | v_bag _ vs1, v_bag _ vs2 => val_bag_metric (val_arr_to_list vs1) (val_arr_to_list vs2)
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
  Eval compute in (val_metric_f (v_arr t_int (val_arr_from_list [v_int 1; v_int 2]%Z))
                                (v_arr t_int (val_arr_from_list [v_int 2]%Z)))%list.
  Eval compute in (val_metric_f (v_arr t_int (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                                (v_arr t_int (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric_f (v_bag t_int (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                                (v_bag t_int (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric_f (v_bag t_int (val_arr_from_list [v_int 1; v_int 2; v_int 3]%list))
                                (v_bag t_int (val_arr_from_list [v_int 3; v_int 2; v_int 1]%list))).

  Definition val_metric : Metric val.
  Proof.
    refine (Build_metric val_metric_f _ _ _).
    {
      apply (val_ind_mut
               (fun x => forall y d, val_metric_f x y = Some d -> (0 <= d)%Z)
               (fun xvs => forall t1 t2 yvs d, (val_metric_f (v_arr t1 xvs) (v_arr t2 yvs) = Some d
                                  -> (0 <= d)%Z)
                                 /\ (val_metric_f (v_bag t1 xvs) (v_bag t2 yvs) = Some d
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
      - intros t xvs IH y d Hd.
        destruct y; inversion Hd as [Hd']; subst; clear Hd.
        destruct (IH t t v d) as [IHarr IHbag].
        simpl in IHarr; apply IHarr; auto.
      - intros t xvs IH y d Hd.
        destruct y.
        + inversion Hd.
        + inversion Hd.
        + inversion Hd.
        + destruct (IH t t v d) as [IHarr IHbag].
          simpl in IHbag; apply IHbag; auto.
      - intros t1 t2 yvs d; simpl.
        split.
        + destruct yvs.
          intros H; inversion H; omega.
          intros contra; inversion contra.
        + destruct yvs; simpl.
          intros H; inversion H; subst; omega.
          intros H; inversion H; subst.
          apply Zle_0_nat.
      - intros v1 IH1 vs1 IH2 t1 t2 vs2 d.
        split.
        + intros Hd; destruct vs2 as [|v2 vs2]; inversion Hd as [Hd']; subst; clear Hd.
          destruct (val_metric_f v1 v2) eqn:Hv;
            destruct (val_arr_metric_f vs1 vs2) eqn:Hvs;
            inversion Hd' as [Hd'']; subst; clear Hd'.
          assert (0 <= z)%Z.
          { apply IH1 with (y := v2); auto. }
          assert (0 <= z0)%Z.
          { destruct (IH2 t1 t2 vs2 z0) as [IHarr IHbag]; apply IHarr; auto. }
          omega.
        + intros Hd; destruct vs2 as [|v2 vs2]; inversion Hd as [Hd']; subst; clear Hd.
          apply Pos2Z.is_nonneg.
          apply Zle_0_nat.
    }
    {
      apply (val_ind_mut
               (fun x => forall y, val_metric_f x y = val_metric_f y x)
               (fun xvs => forall t1 t2 yvs, (val_metric_f (v_arr t1 xvs) (v_arr t2 yvs) =
                                val_metric_f (v_arr t1 yvs) (v_arr t2 xvs))
                               /\ (val_metric_f (v_bag t1 xvs) (v_bag t2 yvs) =
                                  val_metric_f (v_bag t1 yvs) (v_bag t2 xvs)
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
      - intros t xvs IH y.
        destruct y; auto.
        destruct (IH t t v) as [IHarr IHbag].
        apply IHarr; auto.
      - intros t xvs IH y.
        destruct y; auto.
        destruct (IH t t v) as [IHarr IHbag].
        apply IHbag; auto.
      - intros t1 t2 yvs.
        destruct yvs; split; auto.
        simpl.
        unfold bag_metric_f.
        rewrite Nat.add_comm.
        auto.
      - intros v1 IH1 vs1 IH2 t1 t2 vs2; destruct vs2 as [|v2 vs2]; split; auto.
        + simpl; unfold bag_metric_f; rewrite Nat.add_comm; auto.
        + destruct (IH2 t1 t2 vs2) as [IHarr IHbag].
          simpl. simpl in IHarr. rewrite IHarr. rewrite IH1. auto.
        + simpl. unfold bag_metric_f. rewrite Nat.add_comm. auto.
    }
    {
      apply (val_ind_mut
               (fun x => val_metric_f x x = Some 0%Z)
               (fun xvs => forall t1 t2, (val_metric_f (v_arr t1 xvs) (v_arr t2 xvs) = Some 0%Z)
                        /\ (val_metric_f (v_bag t1 xvs) (v_bag t2 xvs) = Some 0%Z))

            ).
      - intros; simpl.
        rewrite Z.sub_diag; auto.
      - intros; simpl.
        destruct (bool_dec b b).
        auto.
        exfalso; apply n; auto.
      - intros t vs IH.
        destruct (IH t t) as [IHarr IHbag]; auto.
      - intros t vs IH.
        destruct (IH t t) as [IHarr IHbag]; auto.
      - auto.
      - intros v IH1 vs IH2 t1 t2;
          destruct (IH2 t1 t2) as [IHarr IHbag];
          split; auto.
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
  Eval compute in (val_metric (v_arr t_int (val_arr_from_list [v_int 1; v_int 2]%Z))
                              (v_arr t_int (val_arr_from_list [v_int 2]%Z)))%list.
  Eval compute in (val_metric (v_arr t_int (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                              (v_arr t_int (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric (v_bag t_int (val_arr_from_list [v_int 1; v_int 2; v_int 3; v_int 4; v_int 5]%Z))
                              (v_bag t_int (val_arr_from_list [v_int 2; v_int 3; v_int 4; v_int 5; v_int 10]%Z)))%list.
  Eval compute in (val_metric (v_bag t_int (val_arr_from_list [v_int 1; v_int 2; v_int 3]%list))
                              (v_bag t_int (val_arr_from_list [v_int 3; v_int 2; v_int 1]%list))).

End Metrics.

Module TS
       (E: Embedding)
       (Lap : Laplace E)
       (LOGIC: APRHL E Lap).

Module APRHLImpl := LOGIC.
Import APRHLImpl SEMImpl LAPImpl CARImpl RP PP MP UP EImpl.

Definition env := VariableDefinitions.VarMap.t Z.
Definition env_get (x : var) (e : env) := VariableDefinitions.VarMap.find x e.
Definition env_set (x : var) (e : env) (d : Z) := VariableDefinitions.VarMap.add x d e.
Definition env_del (x : var) (e : env) := VariableDefinitions.VarMap.remove x e.
Definition env_update (x : var) (e : env) (od : option Z) :=
  match od with
  | Some d => env_set x e d
  | None => env_del x e
  end.
Definition env_from_list (xs: list (var * Z)) :=
  List.fold_right
    (fun x_s senv => env_set (fst x_s) senv (snd x_s))
    (@VariableDefinitions.VarMap.empty Z)
    xs.

Definition denote_env (e : env) : memory_relation :=
  fun m1 m2 => forall x d, VariableDefinitions.VarMap.MapsTo x d e
                   -> exists v1 v2 d', VariableDefinitions.VarMap.MapsTo x v1 m1 /\
                                 VariableDefinitions.VarMap.MapsTo x v2 m2 /\
                                 val_metric v1 v2 = Some d' /\ (d' <= d)%Z.

Definition comb_sens (s1 s2 : option Z) :=
  match s1, s2 with
  | Some s1, Some s2 =>
    if orb (s1 >? 0)%Z (s2 >? 0)%Z
    then None
    else Some 0%Z
  | _, _ => None
  end.

Fixpoint sens_expr (ctx : env) (e : expr) : option Z :=
  match e with
  | e_lit _ => Some 0%Z
  | e_var x => env_get x ctx
  | e_add e1 e2 => lift_option2 Z.add (sens_expr ctx e1) (sens_expr ctx e2)
  | e_minus e1 e2 => lift_option2 Z.add (sens_expr ctx e1) (sens_expr ctx e2)
  | e_mult (e_lit z) e2 => lift_option (Z.mul z) (sens_expr ctx e2)
  | e_mult e1 (e_lit z) => lift_option (fun d => Z.mul d z) (sens_expr ctx e1)
  | e_mult e1 e2 => comb_sens (sens_expr ctx e1) (sens_expr ctx e2)
  | e_div e1 (e_lit z) => lift_option
                           (fun d =>
                              (* Need to round up to account for remainders *)
                              if Z.rem d z =? 0
                              then Z.div d z
                              else (Z.div d z) + 1)%Z
                           (sens_expr ctx e1)
  | e_div e1 e2 => comb_sens (sens_expr ctx e1) (sens_expr ctx e2)
  | e_lt e1 e2 => comb_sens (sens_expr ctx e1) (sens_expr ctx e2)
  | e_eq e1 e2 => comb_sens (sens_expr ctx e1) (sens_expr ctx e2)
  | e_and e1 e2 => comb_sens (sens_expr ctx e1) (sens_expr ctx e2)
  | e_or e1 e2 => comb_sens (sens_expr ctx e1) (sens_expr ctx e2)
                           (* TODO: Fix this *)
  | _ => None
  end.

Lemma sens_expr_sound:
  forall (m1 m2 : memory) (ctx : env) (tctx : st_env) (e : expr) t ed v1 v2,
    (* Everything is welltyped *)
    welltyped_expr tctx e t ->
    welltyped_memory tctx m1 ->
    welltyped_memory tctx m2 ->
    (* Memory satisfies pre-condition *)
    denote_env ctx m1 m2 ->
    (* The expression has bounded sensitivity *)
    sens_expr ctx e = Some ed ->
    (* Evaluating the expressions should yield values with distance less than
       that computed by sens_expr
     *)
    sem_expr m1 e = Some v1 ->
    sem_expr m2 e = Some v2 ->
    exists dv, val_metric_f v1 v2 = Some dv /\ (dv <= ed)%Z.
Proof.
  intros m1 m2 ctx tctx e tau ed v1 v2 Htau_e.
  generalize dependent v2.
  generalize dependent v1.
  generalize dependent ed.
  generalize dependent ctx.
  generalize dependent m2.
  generalize dependent m1.
  induction Htau_e.
  - simpl; intros; subst.
    inversion H2; inversion H3; inversion H4; subst; clear H2; clear H3; clear H4.
    exists 0%Z; simpl.
    split; try omega.
    rewrite Z.sub_diag; auto.
  - intros m1 m2 ctx ed v1 v2 Hm1 Hm2 Hctx Hed Hv1 Hv2.
    simpl in Hed, Hv1, Hv2.
    apply VarMap.find_2 in Hv1.
    apply VarMap.find_2 in Hv2.
    unfold denote_env in Hctx.
    unfold env_get in Hed.
    apply VarMap.find_2 in Hed.
    destruct (Hctx x ed Hed) as [v1' [v2' [d' [Hv1' [Hv2' [Hd' Hdd'] ] ] ] ] ].
    apply VarMap.find_1 in Hv1.
    apply VarMap.find_1 in Hv2.
    apply VarMap.find_1 in Hv1'.
    apply VarMap.find_1 in Hv2'.
    rewrite Hv1 in Hv1'.
    rewrite Hv2 in Hv2'.
    inversion Hv1'; inversion Hv2'; subst; clear Hv1'; clear Hv2'.
    exists d'; auto.
  - intros m1 m2 ctx ed v1 v2 Hm1 Hm2 Hctx Hadd Hv1 Hv2.
    simpl in Hadd, Hv1, Hv2.
    destruct_sem_expr m1 e1; destruct_sem_expr m2 e1;
      destruct_sem_expr m1 e2; destruct_sem_expr m2 e2.
    rewrite H_v_e1 in Hv1; rewrite H_v_e0 in Hv2;
      rewrite H_v_e2 in Hv1; rewrite H_v_e3 in Hv2.
    ty_val v_e1; try (apply sem_expr_val_typed with (env := env0) (e := e1) (m := m1); auto).
    ty_val v_e0; try (apply sem_expr_val_typed with (env := env0) (e := e1) (m := m2); auto).
    ty_val v_e2; try (apply sem_expr_val_typed with (env := env0) (e := e2) (m := m1); auto).
    ty_val v_e3; try (apply sem_expr_val_typed with (env := env0) (e := e2) (m := m2); auto).
    inversion H_type_v_e1;
      inversion H_type_v_e0;
      inversion H_type_v_e2;
      inversion H_type_v_e3;
      subst;
      clear H_type_v_e1;
      clear H_type_v_e0;
      clear H_type_v_e2;
      clear H_type_v_e3.
    inversion Hv1; inversion Hv2; subst; clear Hv1; clear Hv2.
    destruct (sens_expr ctx e1) eqn:Hadd_1;
      destruct (sens_expr ctx e2) eqn:Hadd_2;
      inversion Hadd; subst; clear Hadd.
    destruct (IHHtau_e1 m1 m2 ctx z3 z z0) as [d_add_1 [H_d_add_1 H_d_add_1_z3] ]; auto.
    destruct (IHHtau_e2 m1 m2 ctx z4 z1 z2) as [d_add_2 [H_d_add_2 H_d_add_2_z4] ]; auto.
    simpl. simpl in H_d_add_1, H_d_add_2.
    inversion H_d_add_1; subst; clear H_d_add_1.
    inversion H_d_add_2; subst; clear H_d_add_2.
    exists (Z.abs (z + z1 - (z0 + z2)))%Z; split; try omega; auto.
    assert (Z.abs (z + z1 - (z0 + z2)) <= Z.abs (z - z0) + Z.abs (z1 - z2))%Z.
    {
      rewrite Z.sub_add_distr.
      replace ((z + z1 - z0 - z2))%Z with ((z - z0) + (z1 - z2))%Z by omega.
      apply Z.abs_triangle.
    }
    omega.
  - intros m1 m2 ctx ed v1 v2 Hm1 Hm2 Hctx Hsub Hv1 Hv2.
    simpl in Hv1, Hv2.
    destruct_sem_expr m1 e1;
      destruct_sem_expr m2 e1;
      destruct_sem_expr m1 e2;
      destruct_sem_expr m2 e2.
    rewrite H_v_e1 in Hv1;
      rewrite H_v_e0 in Hv2;
      rewrite H_v_e2 in Hv1;
      rewrite H_v_e3 in Hv2.
    ty_val v_e1; try (apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1); auto).
    ty_val v_e0; try (apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1); auto).
    ty_val v_e2; try (apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto).
    ty_val v_e3; try (apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto).
    inversion H_type_v_e1;
      inversion H_type_v_e0;
      inversion H_type_v_e2;
      inversion H_type_v_e3;
      subst;
      clear H_type_v_e1;
      clear H_type_v_e0;
      clear H_type_v_e2;
      clear H_type_v_e3.
    simpl in Hsub.
    destruct (sens_expr ctx e1) eqn:H_sub1;
      destruct (sens_expr ctx e2) eqn:H_sub2;
      inversion Hsub; subst; clear Hsub.
    destruct (IHHtau_e1 m1 m2 ctx z3 z z0) as [d_sub1 [H_d_sub1 H_d_sub1_ed] ]; auto.
    destruct (IHHtau_e2 m1 m2 ctx z4 z1 z2) as [d_sub2 [H_d_sub2 H_d_sub2_ed] ]; auto.
    inversion Hv1; inversion Hv2; subst; clear Hv1; clear Hv2.
    simpl. exists (Z.abs (z - z1 - (z0 - z2))); split; auto.
    simpl in H_d_sub1, H_d_sub2;
      inversion H_d_sub1;
      inversion H_d_sub2;
      subst;
      clear H_d_sub1; clear H_d_sub2.
    assert (Z.abs (z - z1 - (z0 - z2)) <= Z.abs (z - z0) + Z.abs (z1 - z2))%Z. {
      rewrite Z.sub_sub_distr.
      replace (z - z1 - z0 + z2)%Z with ((z - z0) + (- (z1 - z2)) )%Z by omega.
      replace (Z.abs (z1 - z2)) with (Z.abs (-(z1-z2)))%Z.
      apply Z.abs_triangle.
      apply Z.abs_opp.
    }
    omega.
    (* The cases are easy but tedious... TODO: finish them *)
Admitted.

Lemma env_update_impl :
  forall d d' m1 m2 env x,
    env_get x env = Some d' ->
    (d <= d')%Z ->
    denote_env (env_update x env (Some d)) m1 m2 -> denote_env env m1 m2.
Proof.
  intros d d' m1 m2 env x.
  intros Henv Hlt.
  simpl.
  unfold denote_env.
  intros HP x' dist Hx'.
  destruct (StringDec.eq_dec x x').
  - subst.
    destruct (HP x' d) as [v1 [v2 [vd [Hv1 [Hv2 [Hvd Hvdd] ] ] ] ] ]; auto.
    unfold env_set. apply VarMap.add_1; auto.
    exists v1, v2, vd.
    repeat split; auto.
    apply VarMap.find_1 in Hx'.
    unfold env_get in Henv.
    rewrite Hx' in Henv. inversion Henv; subst; clear Henv.
    omega.
  - destruct (HP x' dist) as [v1 [v2 [vd [Hv1 [Hv2 [Hvd Hvdd] ] ] ] ] ]; auto.
    unfold env_set. apply VarMap.add_2; auto.
    exists v1, v2, vd.
    repeat split; auto.
Qed.

Lemma assign_sound :
  forall (ctx : env) (x : var) (e : expr) d,
    sens_expr ctx e = Some d ->
    ((x <- e) ~_(0%R) (x <- e) : denote_env ctx ==> denote_env (env_update x ctx (Some d)))%triple.
Admitted.

End TS.
