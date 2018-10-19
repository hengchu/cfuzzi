Require Export Cfuzzi.BaseDefinitions.
Require Export Cfuzzi.Logic.
Require Export Cfuzzi.Semantics.

Require Import Coq.Reals.Reals.
Require Import Fourier.

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

Definition env := BaseDefinitions.VarMap.t Z.
Definition env_get (x : var) (e : env) := BaseDefinitions.VarMap.find x e.
Definition env_set (x : var) (e : env) (d : Z) := BaseDefinitions.VarMap.add x d e.
Definition env_del (x : var) (e : env) := BaseDefinitions.VarMap.remove x e.
Definition env_update (x : var) (e : env) (od : option Z) :=
  match od with
  | Some d => env_set x e d
  | None => env_del x e
  end.
Definition env_from_list (xs: list (var * Z)) :=
  List.fold_right
    (fun x_s senv => env_set (fst x_s) senv (snd x_s))
    (@BaseDefinitions.VarMap.empty Z)
    xs.

Definition denote_env (e : env) : memory_relation :=
  fun m1 m2 => forall x d, BaseDefinitions.VarMap.MapsTo x d e
                   -> exists v1 v2 d', BaseDefinitions.VarMap.MapsTo x v1 m1 /\
                                 BaseDefinitions.VarMap.MapsTo x v2 m2 /\
                                 val_metric v1 v2 = Some d' /\ (d' <= d)%Z.

Definition comb_sens (s1 s2 : option Z) :=
  match s1, s2 with
  | Some s1, Some s2 =>
    if orb (s1 >? 0)%Z (s2 >? 0)%Z
    then None
    else Some 0%Z
  | _, _ => None
  end.

Definition max_sens (s1 s2 : option Z) :=
  match s1, s2 with
  | Some s1, Some s2 =>
    Some (Z.max s1 s2)
  | _, _ => None
  end.

Definition env_max (e1 e2 : env) :=
  VarMap.fold (fun x s1 acc =>
                 match BaseDefinitions.VarMap.find x e2 with
                 | None => env_update x acc None
                 | Some s2 => env_update x acc (Some (Z.max s1 s2))
                 end)
              e1
              (@BaseDefinitions.VarMap.empty Z).

Fixpoint sens_expr (ctx: env) (tctx: st_env) (e: expr) : option Z :=
  match e with
  | e_lit _ => Some 0%Z
  | e_var x => env_get x ctx
  | e_add e1 e2 => lift_option2 Z.add (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_minus e1 e2 => lift_option2 Z.add (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_mult (e_lit z) e2 => lift_option (Z.mul z) (sens_expr ctx tctx e2)
  | e_mult e1 (e_lit z) => lift_option (fun d => Z.mul d z) (sens_expr ctx tctx e1)
  | e_mult e1 e2 => comb_sens (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_div e1 (e_lit z) => lift_option
                           (fun d =>
                              (* Need to round up to account for remainders *)
                              if Z.rem d z =? 0
                              then Z.div d z
                              else (Z.div d z) + 1)%Z
                           (sens_expr ctx tctx e1)
  | e_div e1 e2 => comb_sens (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_lt e1 e2 => comb_sens (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_eq e1 e2 => comb_sens (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_and e1 e2 => comb_sens (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_or e1 e2 => comb_sens (sens_expr ctx tctx e1) (sens_expr ctx tctx e2)
  | e_index e1 e2 =>
    match welltyped_expr_compute tctx e1,
          sens_expr ctx tctx e2
    with
    | Some (t_arr _), Some Z0 => sens_expr ctx tctx e1
    | _, _ => None
    end
  | e_length e =>
    match welltyped_expr_compute tctx e,
          sens_expr ctx tctx e
    with
    | Some (t_arr _), Some s => Some 0%Z
    | Some (t_bag _), Some s => Some s
    | _, _ => None
    end
  end.

Lemma related_arr_index: forall vs1 vs2 t1 t2 d,
    val_metric (v_arr t1 vs1) (v_arr t2 vs2) = Some d
    -> (forall idx, (exists v1, val_arr_index vs1 idx = Some v1) <-> (exists v2, val_arr_index vs2 idx = Some v2)).
Proof.
Admitted.

Lemma sens_expr_sound:
  forall (m1 m2 : memory) (ctx : env) (tctx : st_env) (e : expr) t ed v1 v2,
    (* Everything is welltyped *)
    welltyped_expr tctx e t ->
    welltyped_memory tctx m1 ->
    welltyped_memory tctx m2 ->
    (* Memory satisfies pre-condition *)
    denote_env ctx m1 m2 ->
    (* The expression has bounded sensitivity *)
    sens_expr ctx tctx e = Some ed ->
    sem_expr m1 e = Some v1 ->
    sem_expr m2 e = Some v2 ->
    (* Evaluating the expressions should yield values with distance less than
       that computed by sens_expr, and the expressions should co-terminate.
     *)
    exists dv, val_metric_f v1 v2 = Some dv /\ (dv <= ed)%Z.
Proof.
Admitted.

Lemma typed_expr_coterm:
  forall (m1 m2: memory) (ctx: env) (tctx: st_env) (e: expr) t ed,
    welltyped_expr tctx e t ->
    welltyped_memory tctx m1 ->
    welltyped_memory tctx m2 ->
    denote_env ctx m1 m2 ->
    sens_expr ctx tctx e = Some ed ->
    (exists v1, sem_expr m1 e = Some v1) <-> (exists v2, sem_expr m2 e = Some v2).
Proof.
  intros m1 m2 ctx tctx e t ed Het Hm1t Hm2t Hm1m2 Hed.
  generalize dependent ed.
  induction Het.
  - intros ed Hed.
    simpl; split;
      intros [v Hv]; inv Hv; exists z; auto.
  - intros ed Hed.
    simpl. unfold denote_env in Hm1m2.
    simpl in Hed.
    unfold env_get in Hed.
    apply VarMap.find_2 in Hed.
    destruct (Hm1m2 x ed) as [v1 [v2 [d12 [Hv1 [Hv2 [Hv1v2 Hd] ] ] ] ] ]; auto.
    split.
    + exists v2; apply VarMap.find_1; auto.
    + exists v1; apply VarMap.find_1; auto.
  - (* Addition *)
    intros ed Hed.
    simpl in Hed.
    unfold lift_option2 in Hed.
    destruct (sens_expr ctx env0 e1) eqn:He1;
      destruct (sens_expr ctx env0 e2) eqn:He2;
      try (solve [inv Hed] ).
    destruct (IHHet1 Hm1t Hm2t z) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t z0) as [He2_LR He2_RL]; auto.
    split.
    + intros HL. destruct HL as [sum1 Hsum1].
      simpl in Hsum1.
      destruct (sem_expr m1 e1) eqn:Hm1e1; auto;
        destruct (sem_expr m1 e2) eqn:Hm1e2; auto;
          try (solve [inv Hsum1] ).
      assert (Hv_int: welltyped_val v t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1) (v := v) (t := t_int); auto. }
      assert (Hv0_int: welltyped_val v0 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2) (v := v0) (t := t_int); auto. }
      inv Hv_int; inv Hv0_int.
      destruct He1_LR as [v21 Hm2e1]; auto.
      { exists z1; auto. }
      destruct He2_LR as [v22 Hm2e2]; auto.
      { exists z2; auto. }
      assert (Hv21_int: welltyped_val v21 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1) (v := v21) (t := t_int); auto. }
      assert (Hv22_int: welltyped_val v22 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2) (v := v22) (t := t_int); auto. }
      inv Hv21_int; inv Hv22_int.
      exists (z3 + z4)%Z; simpl.
      rewrite Hm2e1; rewrite Hm2e2; auto.
      destruct v; inv Hsum1.
    + intros HR. destruct HR as [sum2 Hsum2].
      simpl in Hsum2.
      destruct (sem_expr m2 e1) eqn:Hm2e1; auto;
        destruct (sem_expr m2 e2) eqn:Hm2e2; auto;
          try (solve [inv Hsum2] ).
      assert (Hv_int: welltyped_val v t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1) (v := v) (t := t_int); auto. }
      assert (Hv0_int: welltyped_val v0 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2) (v := v0) (t := t_int); auto. }
      inv Hv_int; inv Hv0_int.
      destruct He1_RL as [v11 Hm1e1]; auto.
      { exists z1; auto. }
      destruct He2_RL as [v12 Hm1e2]; auto.
      { exists z2; auto. }
      assert (Hv11_int: welltyped_val v11 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1) (v := v11) (t := t_int); auto. }
      assert (Hv12_int: welltyped_val v12 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2) (v := v12) (t := t_int); auto. }
      inv Hv11_int; inv Hv12_int.
      exists (z3 + z4)%Z; simpl.
      rewrite Hm1e1; rewrite Hm1e2; auto.
      destruct v; inv Hsum2.
  - (* Subtraction *)
    intros ed Hed.
    simpl in Hed.
    unfold lift_option2 in Hed.
    destruct (sens_expr ctx env0 e1) eqn:He1;
      destruct (sens_expr ctx env0 e2) eqn:He2;
      try (solve [inv Hed] ).
    destruct (IHHet1 Hm1t Hm2t z) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t z0) as [He2_LR He2_RL]; auto.
    split.
    + intros HL. destruct HL as [sum1 Hsum1].
      simpl in Hsum1.
      destruct (sem_expr m1 e1) eqn:Hm1e1; auto;
        destruct (sem_expr m1 e2) eqn:Hm1e2; auto;
          try (solve [inv Hsum1] ).
      assert (Hv_int: welltyped_val v t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1) (v := v) (t := t_int); auto. }
      assert (Hv0_int: welltyped_val v0 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2) (v := v0) (t := t_int); auto. }
      inv Hv_int; inv Hv0_int.
      destruct He1_LR as [v21 Hm2e1]; auto.
      { exists z1; auto. }
      destruct He2_LR as [v22 Hm2e2]; auto.
      { exists z2; auto. }
      assert (Hv21_int: welltyped_val v21 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1) (v := v21) (t := t_int); auto. }
      assert (Hv22_int: welltyped_val v22 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2) (v := v22) (t := t_int); auto. }
      inv Hv21_int; inv Hv22_int.
      exists (z3 - z4)%Z; simpl.
      rewrite Hm2e1; rewrite Hm2e2; auto.
      destruct v; inv Hsum1.
    + intros HR. destruct HR as [sum2 Hsum2].
      simpl in Hsum2.
      destruct (sem_expr m2 e1) eqn:Hm2e1; auto;
        destruct (sem_expr m2 e2) eqn:Hm2e2; auto;
          try (solve [inv Hsum2] ).
      assert (Hv_int: welltyped_val v t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1) (v := v) (t := t_int); auto. }
      assert (Hv0_int: welltyped_val v0 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2) (v := v0) (t := t_int); auto. }
      inv Hv_int; inv Hv0_int.
      destruct He1_RL as [v11 Hm1e1]; auto.
      { exists z1; auto. }
      destruct He2_RL as [v12 Hm1e2]; auto.
      { exists z2; auto. }
      assert (Hv11_int: welltyped_val v11 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1) (v := v11) (t := t_int); auto. }
      assert (Hv12_int: welltyped_val v12 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2) (v := v12) (t := t_int); auto. }
      inv Hv11_int; inv Hv12_int.
      exists (z3 - z4)%Z; simpl.
      rewrite Hm1e1; rewrite Hm1e2; auto.
      destruct v; inv Hsum2.
  - (* Multiplication *)
    intros ed Hed.
    simpl in Hed.
    unfold lift_option2 in Hed.
    destruct (sens_expr ctx env0 e1) eqn:Hse1;
      destruct (sens_expr ctx env0 e2) eqn:Hse2;
      try (solve [destruct e1; destruct e2;
                  inv Hed] ).
    + unfold comb_sens in Hed.
      destruct (expr_eqdec e1 (e_lit z)).
      * subst. inv Hed.
        destruct (IHHet2 Hm1t Hm2t z0) as [He2_LR He2_RL]; auto.
        {
          split.
          - intros [prod1 Hprod1]. simpl in Hprod1.
            destruct (sem_expr m1 e2) as [v12|] eqn:Hm1e2;
              try (solve [inv Hprod1] ).
            assert (Hv12_int: welltyped_val v12 t_int).
            { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2) (v := v12) (t := t_int)
              ; auto. }
            inv Hv12_int; inv Hprod1.
            destruct He2_LR as [v22 Hv22].
            { exists z1; auto. }
            assert (Hv22_int: welltyped_val v22 t_int).
            { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2) (v := v22) (t := t_int)
              ; auto. }
            inv Hv22_int.
            exists (z * z2)%Z; auto.
            simpl; rewrite Hv22; auto.
          - intros [prod2 Hprod2]. simpl in Hprod2.
            destruct (sem_expr m2 e2) as [v22|] eqn:Hm1e2;
              try (solve [inv Hprod2] ).
            assert (Hv22_int: welltyped_val v22 t_int).
            { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2) (v := v22) (t := t_int)
              ; auto. }
            inv Hv22_int; inv Hprod2.
            destruct He2_RL as [v12 Hv12].
            { exists z1; auto. }
            assert (Hv12_int: welltyped_val v12 t_int).
            { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2) (v := v12) (t := t_int)
              ; auto. }
            inv Hv12_int.
            exists (z * z2)%Z; auto.
            simpl; rewrite Hv12; auto.
        }
      * unfold lift_option in Hed.
        destruct (IHHet1 Hm1t Hm2t z) as [He1_LR He1_RL]; auto.
        destruct (IHHet2 Hm1t Hm2t z0) as [He2_LR He2_RL]; auto.
        split.
        ** intros [prod1 Hprod1].
           simpl in Hprod1.
           destruct (sem_expr m1 e1) eqn:Hm1e1;
             destruct (sem_expr m1 e2) eqn:Hm1e2;
             try (solve [inv Hprod1] ).
           assert (H_v_int: welltyped_val v t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m1) (e := e1) (v := v) (t := t_int);
               auto. }
           assert (H_v0_int: welltyped_val v0 t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m1) (e := e2) (v := v0) (t := t_int);
               auto. }
           inv H_v_int; inv H_v0_int; inv Hprod1.
           destruct He1_LR as [v21 Hv21].
           { exists z1; auto. }
           destruct He2_LR as [v22 Hv22].
           { exists z2; auto. }
           simpl; rewrite Hv21, Hv22.
           assert (Hv21_int: welltyped_val v21 t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m2) (e := e1) (v := v21) (t := t_int); auto.
           }
           assert (Hv22_int: welltyped_val v22 t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m2) (e := e2) (v := v22) (t := t_int); auto.
           }
           inv Hv21_int; inv Hv22_int.
           exists (z3 * z4)%Z; auto.
           destruct v; inv Hprod1.
        ** intros [prod2 Hprod2].
           simpl in Hprod2.
           destruct (sem_expr m2 e1) eqn:Hm2e1;
             destruct (sem_expr m2 e2) eqn:Hm2e2;
             try (solve [inv Hprod2] ).
           assert (H_v_int: welltyped_val v t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m2) (e := e1) (v := v) (t := t_int);
               auto. }
           assert (H_v0_int: welltyped_val v0 t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m2) (e := e2) (v := v0) (t := t_int);
               auto. }
           inv H_v_int; inv H_v0_int; inv Hprod2.
           destruct He1_RL as [v11 Hv11].
           { exists z1; auto. }
           destruct He2_RL as [v12 Hv12].
           { exists z2; auto. }
           simpl; rewrite Hv11, Hv12.
           assert (Hv11_int: welltyped_val v11 t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m1) (e := e1) (v := v11) (t := t_int); auto.
           }
           assert (Hv12_int: welltyped_val v12 t_int).
           { apply sem_expr_val_typed
               with (env := env0) (m := m1) (e := e2) (v := v12) (t := t_int); auto.
           }
           inv Hv11_int; inv Hv12_int.
           exists (z3 * z4)%Z; auto.
           destruct v; inv Hprod2.
    + unfold lift_option in Hed.
      unfold comb_sens in Hed.
      destruct e2; try (solve [destruct e1; inv Hed] ).
      destruct (IHHet1 Hm1t Hm2t z) as [He1_LR He1_RL]; auto.
      split.
      * intros [prod1 Hprod1].
        simpl in Hprod1.
        destruct (sem_expr m1 e1) as [v11|] eqn:Hv11; try (solve [inv Hprod1] ).
        assert (Hv11_int: welltyped_val v11 t_int).
        { apply sem_expr_val_typed
            with (env := env0) (m := m1) (e := e1) (v := v11) (t := t_int);
            auto. }
        inv Hv11_int; inv Hprod1.
        destruct He1_LR as [v21 Hv21].
        { exists z1; auto. }
        assert (Hv21_int: welltyped_val v21 t_int).
        { apply sem_expr_val_typed
            with (env := env0) (m := m2) (e := e1) (v := v21) (t := t_int);
            auto. }
        inv Hv21_int.
        exists (z2 * z0)%Z; simpl; rewrite Hv21; auto.
      * intros [prod2 Hprod2].
        simpl in Hprod2.
        destruct (sem_expr m2 e1) as [v21|] eqn:Hv21; try (solve [inv Hprod2] ).
        assert (Hv21_int: welltyped_val v21 t_int).
        { apply sem_expr_val_typed
            with (env := env0) (m := m2) (e := e1) (v := v21) (t := t_int);
            auto. }
        inv Hv21_int; inv Hprod2.
        destruct He1_RL as [v11 Hv11].
        { exists z1; auto. }
        assert (Hv11_int: welltyped_val v11 t_int).
        { apply sem_expr_val_typed
            with (env := env0) (m := m1) (e := e1) (v := v11) (t := t_int);
            auto. }
        inv Hv11_int.
        exists (z2 * z0)%Z; simpl; rewrite Hv11; auto.
    + unfold lift_option in Hed.
      unfold comb_sens in Hed.
      destruct e1; try (solve [destruct e2; inv Hed] ).
      destruct (IHHet2 Hm1t Hm2t z) as [He2_LR He2_RL]; auto.
      split.
      * intros [prod1 Hprod1].
        simpl in Hprod1.
        destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
          try (solve [inv Hprod1] ).
        assert (Hv12_int: welltyped_val v12 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
        inv Hv12_int; inv Hprod1.
        destruct He2_LR as [v22 Hv22].
        { exists z1; auto. }
        assert (Hv22_int: welltyped_val v22 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
        inv Hv22_int.
        simpl. rewrite Hv22. exists (z0 * z2)%Z; auto.
      * intros [prod2 Hprod2].
        simpl in Hprod2.
        destruct (sem_expr m2 e2) as [v22|] eqn:Hv22;
          try (solve [inv Hprod2] ).
        assert (Hv22_int: welltyped_val v22 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
        inv Hv22_int; inv Hprod2.
        destruct He2_RL as [v12 Hv12].
        { exists z1; auto. }
        assert (Hv12_int: welltyped_val v12 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
        inv Hv12_int.
        simpl. rewrite Hv12. exists (z0 * z2)%Z; auto.
  - (* Division *)
    intros ed Hed.
    simpl in Hed.
    unfold lift_option, comb_sens in Hed.
    destruct (sens_expr ctx env0 e1) eqn:Hse1;
      destruct (sens_expr ctx env0 e2) eqn:Hse2;
      try (solve [destruct e2; inv Hed] ).
    * destruct (IHHet1 Hm1t Hm2t z) as [He1_LR He1_RL]; auto.
      destruct (IHHet2 Hm1t Hm2t z0) as [He2_LR He2_RL]; auto.
      split.
      ** intros [div1 Hdiv1].
         simpl in Hdiv1.
         destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
           destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
           try (solve [inv Hdiv1] ).
         assert (Hv11_int: welltyped_val v11 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m1) (e := e1); auto.
         }
         assert (Hv12_int: welltyped_val v12 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m1) (e := e2); auto.
         }
         inv Hv11_int; inv Hv12_int; inv Hdiv1.
         destruct He1_LR as [v21 Hv21].
         { exists z1; auto. }
         assert (Hv21_int: welltyped_val v21 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m2) (e := e1); auto.
         }
         destruct He2_LR as [v22 Hv22].
         { exists z2; auto. }
         assert (Hv22_int: welltyped_val v22 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m2) (e := e2); auto.
         }
         inv Hv21_int; inv Hv22_int.
         simpl; rewrite Hv21, Hv22; exists (z3 / z4)%Z; auto.
         destruct v11; inv Hdiv1.
      ** intros [div2 Hdiv2].
         simpl in Hdiv2.
         destruct (sem_expr m2 e1) as [v21|] eqn:Hv21;
           destruct (sem_expr m2 e2) as [v22|] eqn:Hv22;
           try (solve [inv Hdiv2] ).
         assert (Hv21_int: welltyped_val v21 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m2) (e := e1); auto.
         }
         assert (Hv22_int: welltyped_val v22 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m2) (e := e2); auto.
         }
         inv Hv21_int; inv Hv22_int; inv Hdiv2.
         destruct He1_RL as [v11 Hv11].
         { exists z1; auto. }
         assert (Hv11_int: welltyped_val v11 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m1) (e := e1); auto.
         }
         destruct He2_RL as [v12 Hv12].
         { exists z2; auto. }
         assert (Hv12_int: welltyped_val v12 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m1) (e := e2); auto.
         }
         inv Hv11_int; inv Hv12_int.
         simpl; rewrite Hv11, Hv12; exists (z3 / z4)%Z; auto.
         destruct v21; inv Hdiv2.
    * destruct (IHHet1 Hm1t Hm2t z) as [He1_LR He1_RL]; auto.
      assert (He2: exists z2, e2 = e_lit z2).
      {
        destruct e2; try solve [inv Hed].
        exists z0; auto.
      }
      destruct He2 as [z2 He2]; subst.
      split.
      ** intros [div1 Hdiv1].
         simpl in Hdiv1.
         destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
           try (solve [inv Hdiv1] ).
         assert (Hv11_int: welltyped_val v11 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m1) (e := e1) (v := v11); auto. }
         inv Hv11_int; inv Hdiv1.
         destruct He1_LR as [v21 Hv21].
         { exists z0; auto. }
         assert (Hv21_int: welltyped_val v21 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m2) (e := e1) (v := v21); auto. }
         inv Hv21_int.
         simpl; rewrite Hv21.
         exists (z1 / z2)%Z; auto.
      ** intros [div2 Hdiv2].
         simpl in Hdiv2.
         destruct (sem_expr m2 e1) as [v21|] eqn:Hv21;
           try (solve [inv Hdiv2] ).
         assert (Hv21_int: welltyped_val v21 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m2) (e := e1) (v := v21); auto. }
         inv Hv21_int; inv Hdiv2.
         destruct He1_RL as [v11 Hv11].
         { exists z0; auto. }
         assert (Hv11_int: welltyped_val v11 t_int).
         { apply sem_expr_val_typed
             with (env := env0) (m := m1) (e := e1) (v := v11); auto. }
         inv Hv11_int.
         simpl; rewrite Hv11.
         exists (z1 / z2)%Z; auto.
  - (* Lt *)
    intros ed Hed.
    simpl in Hed.
    unfold comb_sens in Hed.
    destruct (sens_expr ctx env0 e1) as [s1|] eqn:Hes1;
      destruct (sens_expr ctx env0 e2) as [s2|] eqn:Hes2;
      try (solve [inv Hed] ).
    destruct (IHHet1 Hm1t Hm2t s1) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t s2) as [He2_LR He2_RL]; auto.
    split.
    + intros [b1 Hb1].
      simpl in Hb1.
      destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
        destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
        try (solve [inv Hb1] ).
      assert (Hv11_int: welltyped_val v11 t_int).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e1) (v := v11); auto. }
      assert (Hv12_int: welltyped_val v12 t_int).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e2) (v := v12); auto. }
      inv Hv11_int; inv Hv12_int.
      destruct He1_LR as [v21 Hv21].
      { exists z; auto. }
      destruct He2_LR as [v22 Hv22].
      { exists z0; auto. }
      assert (Hv21_int: welltyped_val v21 t_int).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e1); auto. }
      assert (Hv22_int: welltyped_val v22 t_int).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e2); auto. }
      inv Hv21_int; inv Hv22_int.
      simpl.
      rewrite Hv21, Hv22. exists (z1 <? z2)%Z; auto.
      destruct v11; inv Hb1.
    + intros [b2 Hb2].
      simpl in Hb2.
      destruct (sem_expr m2 e1) as [v21|] eqn:Hv21;
        destruct (sem_expr m2 e2) as [v22|] eqn:Hv22;
        try (solve [inv Hb2] ).
      assert (Hv21_int: welltyped_val v21 t_int).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e1) (v := v21); auto. }
      assert (Hv22_int: welltyped_val v22 t_int).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e2) (v := v22); auto. }
      inv Hv21_int; inv Hv22_int.
      destruct He1_RL as [v11 Hv11].
      { exists z; auto. }
      destruct He2_RL as [v12 Hv12].
      { exists z0; auto. }
      assert (Hv11_int: welltyped_val v11 t_int).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e1); auto. }
      assert (Hv12_int: welltyped_val v12 t_int).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e2); auto. }
      inv Hv11_int; inv Hv12_int.
      simpl.
      rewrite Hv11, Hv12. exists (z1 <? z2)%Z; auto.
      destruct v21; inv Hb2.
  - (* Eq *)
    intros ed Hed.
    simpl in Hed. unfold comb_sens in Hed.
    destruct (sens_expr ctx env0 e1) as [s1|] eqn:Hes1;
      destruct (sens_expr ctx env0 e2) as [s2|] eqn:Hes2;
      try (solve [inv Hed] ).
    destruct (IHHet1 Hm1t Hm2t s1) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t s2) as [He2_LR He2_RL]; auto.
    split.
    + intros [eq1 Heq1].
      simpl in Heq1.
      destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
        destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
        try (solve [inv Heq1] ).
      destruct H; subst.
      * assert (Hv11_int: welltyped_val v11 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1); auto. }
        assert (Hv12_int: welltyped_val v12 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
        inv Hv11_int; inv Hv12_int.
        destruct He1_LR as [v21 Hv21].
        { exists z; auto. }
        destruct He2_LR as [v22 Hv22].
        { exists z0; auto. }
        simpl.
        assert (Hv21_int: welltyped_val v21 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1); auto. }
        assert (Hv22_int: welltyped_val v22 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
        inv Hv21_int; inv Hv22_int.
        rewrite Hv21, Hv22.
        exists (z1 =? z2)%Z; auto.
      * assert (Hv11_bool: welltyped_val v11 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1); auto. }
        assert (Hv12_bool: welltyped_val v12 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
        inv Hv11_bool; inv Hv12_bool.
        destruct He1_LR as [v21 Hv21].
        { exists b; auto. }
        destruct He2_LR as [v22 Hv22].
        { exists b0; auto. }
        simpl.
        assert (Hv21_bool: welltyped_val v21 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1); auto. }
        assert (Hv22_bool: welltyped_val v22 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
        inv Hv21_bool; inv Hv22_bool.
        rewrite Hv21, Hv22.
        exists (eqb b1 b2)%Z; auto.
      * destruct v11; inv Heq1.
    + intros [eq2 Heq2].
      simpl in Heq2.
      destruct (sem_expr m2 e1) as [v21|] eqn:Hv21;
        destruct (sem_expr m2 e2) as [v22|] eqn:Hv22;
        try (solve [inv Heq2] ).
      destruct H; subst.
      * assert (Hv21_int: welltyped_val v21 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1); auto. }
        assert (Hv22_int: welltyped_val v22 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
        inv Hv21_int; inv Hv22_int.
        destruct He1_RL as [v11 Hv11].
        { exists z; auto. }
        destruct He2_RL as [v12 Hv12].
        { exists z0; auto. }
        simpl.
        assert (Hv11_int: welltyped_val v11 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1); auto. }
        assert (Hv12_int: welltyped_val v12 t_int).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
        inv Hv11_int; inv Hv12_int.
        rewrite Hv11, Hv12.
        exists (z1 =? z2)%Z; auto.
      * assert (Hv21_bool: welltyped_val v21 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1); auto. }
        assert (Hv22_bool: welltyped_val v22 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
        inv Hv21_bool; inv Hv22_bool.
        destruct He1_RL as [v11 Hv11].
        { exists b; auto. }
        destruct He2_RL as [v12 Hv12].
        { exists b0; auto. }
        simpl.
        assert (Hv11_bool: welltyped_val v11 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1); auto. }
        assert (Hv12_bool: welltyped_val v12 t_bool).
        { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
        inv Hv11_bool; inv Hv12_bool.
        rewrite Hv11, Hv12.
        exists (eqb b1 b2)%Z; auto.
      * destruct v21; inv Heq2.
  - (* And *)
    intros ed Hed.
    simpl in Hed.
    unfold comb_sens in Hed.
    destruct (sens_expr ctx env0 e1) as [s1|] eqn:Hes1;
      destruct (sens_expr ctx env0 e2) as [s2|] eqn:Hes2;
      try (solve [inv Hed] ).
    destruct (IHHet1 Hm1t Hm2t s1) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t s2) as [He2_LR He2_RL]; auto.
    split.
    + intros [b1 Hb1].
      simpl in Hb1.
      destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
        destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
        try (solve [inv Hb1] ).
      assert (Hv11_bool: welltyped_val v11 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e1) (v := v11); auto. }
      assert (Hv12_bool: welltyped_val v12 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e2) (v := v12); auto. }
      inv Hv11_bool; inv Hv12_bool.
      destruct He1_LR as [v21 Hv21].
      { exists b; auto. }
      destruct He2_LR as [v22 Hv22].
      { exists b0; auto. }
      assert (Hv21_bool: welltyped_val v21 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e1); auto. }
      assert (Hv22_bool: welltyped_val v22 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e2); auto. }
      inv Hv21_bool; inv Hv22_bool.
      simpl.
      rewrite Hv21, Hv22. exists (b2 && b3); auto.
      destruct v11; inv Hb1.
    + intros [b2 Hb2].
      simpl in Hb2.
      destruct (sem_expr m2 e1) as [v21|] eqn:Hv21;
        destruct (sem_expr m2 e2) as [v22|] eqn:Hv22;
        try (solve [inv Hb2] ).
      assert (Hv21_bool: welltyped_val v21 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e1) (v := v21); auto. }
      assert (Hv22_bool: welltyped_val v22 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e2) (v := v22); auto. }
      inv Hv21_bool; inv Hv22_bool.
      destruct He1_RL as [v11 Hv11].
      { exists b; auto. }
      destruct He2_RL as [v12 Hv12].
      { exists b0; auto. }
      assert (Hv11_bool: welltyped_val v11 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e1); auto. }
      assert (Hv12_bool: welltyped_val v12 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e2); auto. }
      inv Hv11_bool; inv Hv12_bool.
      simpl.
      rewrite Hv11, Hv12. exists (b1 && b3); auto.
      destruct v21; inv Hb2.
  - (* Or *)
    intros ed Hed.
    simpl in Hed.
    unfold comb_sens in Hed.
    destruct (sens_expr ctx env0 e1) as [s1|] eqn:Hes1;
      destruct (sens_expr ctx env0 e2) as [s2|] eqn:Hes2;
      try (solve [inv Hed] ).
    destruct (IHHet1 Hm1t Hm2t s1) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t s2) as [He2_LR He2_RL]; auto.
    split.
    + intros [b1 Hb1].
      simpl in Hb1.
      destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
        destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
        try (solve [inv Hb1] ).
      assert (Hv11_bool: welltyped_val v11 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e1) (v := v11); auto. }
      assert (Hv12_bool: welltyped_val v12 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e2) (v := v12); auto. }
      inv Hv11_bool; inv Hv12_bool.
      destruct He1_LR as [v21 Hv21].
      { exists b; auto. }
      destruct He2_LR as [v22 Hv22].
      { exists b0; auto. }
      assert (Hv21_bool: welltyped_val v21 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e1); auto. }
      assert (Hv22_bool: welltyped_val v22 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e2); auto. }
      inv Hv21_bool; inv Hv22_bool.
      simpl.
      rewrite Hv21, Hv22. exists (b2 || b3); auto.
      destruct v11; inv Hb1.
    + intros [b2 Hb2].
      simpl in Hb2.
      destruct (sem_expr m2 e1) as [v21|] eqn:Hv21;
        destruct (sem_expr m2 e2) as [v22|] eqn:Hv22;
        try (solve [inv Hb2] ).
      assert (Hv21_bool: welltyped_val v21 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e1) (v := v21); auto. }
      assert (Hv22_bool: welltyped_val v22 t_bool).
      { apply sem_expr_val_typed with (m := m2) (env := env0) (e := e2) (v := v22); auto. }
      inv Hv21_bool; inv Hv22_bool.
      destruct He1_RL as [v11 Hv11].
      { exists b; auto. }
      destruct He2_RL as [v12 Hv12].
      { exists b0; auto. }
      assert (Hv11_bool: welltyped_val v11 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e1); auto. }
      assert (Hv12_bool: welltyped_val v12 t_bool).
      { apply sem_expr_val_typed with (m := m1) (env := env0) (e := e2); auto. }
      inv Hv11_bool; inv Hv12_bool.
      simpl.
      rewrite Hv11, Hv12. exists (b1 || b3); auto.
      destruct v21; inv Hb2.
  - (* Index array *)
    intros ed Hed.
    simpl in Hed.
    rewrite welltyped_expr_iff in Het1.
    rewrite Het1 in Hed.
    rewrite <- welltyped_expr_iff in Het1.
    destruct (sens_expr ctx env0 e2) as [s2|] eqn:Hs2;
      try (solve [inv Hs2] ).
    destruct (Z.eq_dec s2 0)%Z;
      subst;
      try (solve [inv Hs2] ).
    destruct (IHHet1 Hm1t Hm2t ed) as [He1_LR He1_RL]; auto.
    destruct (IHHet2 Hm1t Hm2t 0%Z) as [He2_LR He2_RL]; auto.
    split.
    + intros [idx1 Hidx1].
      simpl in Hidx1.
      destruct (sem_expr m1 e1) as [v11|] eqn:Hv11;
        destruct (sem_expr m1 e2) as [v12|] eqn:Hv12;
        try (solve [inv Hidx1] ).
      assert (Hv11_arr: welltyped_val v11 (t_arr t)).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e1); auto. }
      assert (Hv12_int: welltyped_val v12 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m1) (e := e2); auto. }
      inv Hv12_int. destruct v11; try (solve [inv Hv11_arr] ).
      simpl.
      destruct He1_LR as [v21 Hv21].
      { exists (v_arr t0 v); auto. }
      destruct He2_LR as [v22 Hv22].
      { exists z; auto. }
      assert (Hv21_arr: welltyped_val v21 (t_arr t)).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e1); auto. }
      assert (Hv22_int: welltyped_val v22 t_int).
      { apply sem_expr_val_typed with (env := env0) (m := m2) (e := e2); auto. }
      rewrite Hv21, Hv22.
      destruct v21; try (solve [inv Hv21_arr] ).
      inv Hv22_int.
      assert (Hdv: exists dv, val_metric (v_arr t0 v) (v_arr t1 v0) = Some dv /\ (dv <= ed)%Z).
      { apply sens_expr_sound
          with (m1 := m1) (m2 := m2) (ctx := ctx) (tctx := env0) (e := e1) (t := t_arr t); auto. }
      destruct Hdv as [dv [Hdv1 Hdv2] ].
      destruct (related_arr_index v v0 t0 t1 dv) with (idx := z) as [H_idx_LR H_idx_RL]; auto.
Admitted.
(*
  - (* Index bag *)
    intros ed Hed.
    simpl in Hed.
    rewrite welltyped_expr_iff in Het1.
    rewrite Het1 in Hed; inv Hed.
  - (* Length array *) admit.
  - (* Length bag *) admit.
*)


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

Lemma mvs_inf_sound:
  forall senv stenv c,
    welltyped stenv c
    -> (stenv ⊕ stenv |- c ~_(0%R) c
                       : denote_env senv ==> denote_env
                                    (VarSet.fold
                                       (fun x senv => env_update x senv None)
                                       (mvs c)
                                       senv))%triple.
Proof.
Admitted.

Lemma assign_sound :
  forall (ctx : env) (tctxt: st_env) (x : var) (e : expr) d,
    sens_expr ctx tctxt e = Some d ->
    (tctxt ⊕ tctxt |- (x <- e) ~_( 0%R) (x <- e) : denote_env ctx ==> denote_env (env_update x ctx (Some d)))%triple.
Admitted.

Lemma bool_0_same:
  forall senv stenv e,
    welltyped_expr stenv e t_bool
    -> sens_expr senv stenv e = Some 0%Z
    -> forall m1 m2, welltyped_memory stenv m1
               -> welltyped_memory stenv m2
               -> sem_expr m1 e = sem_expr m2 e.
Proof.
Admitted.

Lemma env_max_impl_1:
  forall env1 env2,
  forall m1 m2, denote_env env1 m1 m2 -> denote_env (env_max env1 env2) m1 m2.
Proof.
Admitted.

Lemma env_max_impl_2:
  forall env1 env2,
  forall m1 m2, denote_env env2 m1 m2 -> denote_env (env_max env1 env2) m1 m2.
Proof.
Admitted.

Lemma env_equal_Equal:
  forall env1 env2,
    VarMap.equal Z.eqb env1 env2 = true
    -> VarMap.Equal env1 env2.
Proof.
  intros env1 env2 Hequal.
  unfold VarMap.Equal.
  intros y.
  apply VarMap.equal_2 in Hequal.
  unfold VarMap.Equivb in Hequal.
  unfold VarMap.Raw.Equivb in Hequal.
  inv Hequal.
  destruct (BaseDefinitions.VarMap.find y env1) as [yv1|] eqn:Hy1;
    destruct (BaseDefinitions.VarMap.find y env2) as [yv2|] eqn:Hy2;
    auto.
  - apply VarMap.find_2 in Hy1.
    apply VarMap.find_2 in Hy2.
    f_equal.
    rewrite <- Z.eqb_eq.
    apply H0 with (k := y); auto.
  - apply VarMap.find_2 in Hy1.
    unfold VarMap.MapsTo in Hy1.
    unfold VarMap.Raw.PX.In in H.
    destruct (H y) as [H_LR H_RL].
    destruct H_LR as [yv2 Hyv2].
    { exists yv1; auto. }
    apply VarMap.find_1 in Hyv2.
    rewrite Hy2 in Hyv2.
    inv Hyv2.
  - apply VarMap.find_2 in Hy2.
    unfold VarMap.MapsTo in Hy2.
    unfold VarMap.Raw.PX.In in H.
    destruct (H y) as [H_LR H_RL].
    destruct H_RL as [yv1 Hyv1].
    { exists yv2; auto. }
    apply VarMap.find_1 in Hyv1.
    rewrite Hy1 in Hyv1.
    inv Hyv1.
Qed.

Hint Resolve env_equal_Equal.

Add Parametric Morphism (m1 m2: memory) : (fun env => denote_env env m1 m2)
    with signature (@VarMap.Equal Z) ==> ( iff )
      as denote_env_equal_inv.
Proof.
  intros env1 env2 Heq.
  split.
  - intros H. unfold denote_env in *.
    intros y d Hyd. unfold VarMap.Equal in Heq.
    apply VarMap.find_1 in Hyd.
    rewrite <- Heq in Hyd.
    apply VarMap.find_2 in Hyd.
    destruct (H y d Hyd) as [v1 [v2 [vd [Hyv1 [Hyv2 [Hv Hd] ] ] ] ] ].
    exists v1, v2, vd; repeat split; auto.
  - intros H. unfold denote_env in *.
    intros y d Hyd. unfold VarMap.Equal in Heq.
    apply VarMap.find_1 in Hyd.
    rewrite Heq in Hyd.
    apply VarMap.find_2 in Hyd.
    destruct (H y d Hyd) as [v1 [v2 [vd [Hyv1 [Hyv2 [Hv Hd] ] ] ] ] ].
    exists v1, v2, vd; repeat split; auto.
Qed.

Lemma env_equal_inv1:
  forall stenv c eps env1 env2 env1' env2',
    VarMap.Equal env1 env1'
    -> VarMap.Equal env2 env2'
    -> welltyped stenv c
    -> (stenv ⊕ stenv |- c ~_(eps) c : denote_env env1 ==> denote_env env2)%triple
    -> (stenv ⊕ stenv |- c ~_(eps) c : denote_env env1' ==> denote_env env2')%triple.
Proof.
  intros stenv c eps env1 env2 env1' env2'.
  intros Heq1 Heq2 Ht Haprhl.
  eapply aprhl_conseq; eauto.
  - intros m1 m2 Hm1t Hm2t Hm1m2'.
    rewrite denote_env_equal_inv; eauto.
  - intros m1 m2 Hm1t Hm2t Hm1m2.
    rewrite <- denote_env_equal_inv.
    apply Hm1m2; auto.
    apply Heq2.
  - fourier.
Qed.

Lemma env_equal_inv2:
  forall stenv c eps env1 env2 env1' env2',
    VarMap.Equal env1 env1'
    -> VarMap.Equal env2 env2'
    -> welltyped stenv c
    -> (stenv ⊕ stenv |- c ~_(eps) c : denote_env env1' ==> denote_env env2')%triple
    -> (stenv ⊕ stenv |- c ~_(eps) c : denote_env env1 ==> denote_env env2)%triple.
Proof.
  intros stenv c eps env1 env2 env1' env2'.
  intros Heq1 Heq2 Ht Haprhl.
  eapply aprhl_conseq; eauto.
  - intros m1 m2 Hm1t Hm2t Hm1m2'.
    rewrite <- denote_env_equal_inv.
    apply Hm1m2'.
    auto.
  - intros m1 m2 Hm1t Hm2t Hm1m2.
    rewrite denote_env_equal_inv.
    apply Hm1m2.
    auto.
  - fourier.
Qed.

End TS.
