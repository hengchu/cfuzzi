Require Export Coq.Classes.Morphisms.

Require Export Cfuzzi.Lib.
Require Export Cfuzzi.VariableDefinitions.
Require Export Cfuzzi.Syntax.
Require Export Cfuzzi.SimpleTypeSystem.

Require Export Setoid.

Require Export Program.

Module Type SEM (E : Embedding) (LAP : Laplace(E)).
  Module LAPImpl := LAP.
  Import LAPImpl CARImpl RP PP MP UP EImpl.

  Definition memory := VarMap.t val.
  Definition mem_get := @VarMap.find val.
  Definition mem_set := @VarMap.add val.

  Definition welltyped_memory (env : st_env) (m : memory) :=
    forall x t, VarMap.MapsTo x t env -> exists v, VarMap.MapsTo x v m /\ welltyped_val v t.

  Parameter welltyped_memory_equiv_inv :
    forall env m1 m2,
      welltyped_memory env m1
      -> VarMap.Equal m1 m2
      -> welltyped_memory env m2.

  Parameter welltyped_memory_add :
    forall env m x v t,
      welltyped_memory env m
      -> VarMap.MapsTo x t env
      -> welltyped_val v t
      -> welltyped_memory env (VarMap.add x v m).

  Parameter sem_expr : memory -> expr -> option val.

  Parameter sem_expr_val_typed : forall env m e v t,
    welltyped_expr env e t
    -> sem_expr m e = Some v
    -> welltyped_memory env m
    -> welltyped_val v t.

  Parameter sem_welltyped_expr : forall env m e t,
    welltyped_expr env e t
    -> welltyped_memory env m
    -> exists v, sem_expr m e = Some v.

  Parameter step_base_instr : memory -> base_instr -> distr memory.
  Parameter step_cmd : memory -> cmd -> distr (cmd * memory).

  Parameter step_welltyped_cmd_preservation : forall env m c,
    welltyped env c
    -> welltyped_memory env m
    -> range (fun cm => welltyped env (fst cm)
                    /\ welltyped_memory env (snd cm)) (step_cmd m c).

  Parameter step_trans : memory -> cmd -> nat -> distr (cmd * memory).
  Parameter step_welltyped_trans_preservation : forall env m c n,
      welltyped env c
      -> welltyped_memory env m
      -> range (fun cm => welltyped env (fst cm)
                      /\ welltyped_memory env (snd cm)) (step_trans m c n).

  Parameter final : cmd -> bool.
  Parameter step_star : memory -> cmd -> nat -> distr memory.
  Parameter step_welltyped_star_preservation : forall env m c n,
    welltyped env c
    -> welltyped_memory env m
    -> range (fun m => welltyped_memory env m) (step_star m c n).
  Parameter step_star_monotonic : forall (c : cmd) (m : memory) (j k: nat),
      (j <= k)%nat
      -> le_distr (step_star m c j) (step_star m c k).

  Parameter deno : cmd -> memory -> distr memory.
  Notation "'[[' c ']]'" := (deno c) (at level 65).

  Definition lossless (c : cmd) :=
    forall m, mu ([[ c ]] m) (fun _ => 1%U) == 1%U.
End SEM.

Module Make (E : Embedding) (LAP : Laplace(E)) <: SEM(E)(LAP)
    with Module LAPImpl := LAP.
Module LAPImpl := LAP.
Import LAPImpl CARImpl RP PP MP UP EImpl.

Definition memory := VarMap.t val.
Definition mem_get := @VarMap.find val.
Definition mem_set := @VarMap.add val.

Definition welltyped_memory (env : st_env) (m : memory) :=
  forall x t, VarMap.MapsTo x t env -> exists v, VarMap.MapsTo x v m /\ welltyped_val v t.

Lemma welltyped_memory_equiv_inv : forall env m1 m2,
    welltyped_memory env m1
    -> VarMap.Equal m1 m2
    -> welltyped_memory env m2.
Proof.
  intros env m1 m2 Hm1 Hequal.
  unfold welltyped_memory, VarMap.Equal in *.
  intros x t Hxt.
  destruct (Hm1 x t Hxt) as [v [Hv Hv_t]].
  exists v; split; auto.
  apply VarMap.find_1 in Hv.
  rewrite Hequal in Hv.
  apply VarMap.find_2 in Hv; auto.
Qed.

Lemma welltyped_memory_add : forall env m x v t,
    welltyped_memory env m
    -> VarMap.MapsTo x t env
    -> welltyped_val v t
    -> welltyped_memory env (VarMap.add x v m).
Proof.
  intros env m x v t Hm Hxt Hvt.
  unfold welltyped_memory in *.
  intros x' t' Hxt'.
  destruct (StringDec.eq_dec x x').
  + subst.
    apply VarMap.find_1 in Hxt.
    apply VarMap.find_1 in Hxt'.
    rewrite Hxt in Hxt'; inversion Hxt'; subst; clear Hxt'.
    exists v; split; auto.
    apply VarMap.add_1; auto.
  + destruct (Hm x' t') as [v' [Hxv' Hvt']]; auto.
    exists v'; split; auto.
    apply VarMap.add_2; auto.
Qed.

Hint Unfold welltyped_memory.
Hint Resolve welltyped_memory_add.
Hint Resolve welltyped_memory_equiv_inv.

Fixpoint sem_expr (m : memory) (e : expr) : option val :=
  match e with
  | e_lit z => Some (v_int z)
  | e_var x => VarMap.find x m
  | e_add e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_int v1), Some (v_int v2) => Some (v_int (v1 + v2)%Z)
    | _, _ => None
    end
  | e_minus e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_int v1), Some (v_int v2) => Some (v_int (v1 - v2)%Z)
    | _, _ => None
    end
  | e_mult e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_int v1), Some (v_int v2) => Some (v_int (v1 * v2)%Z)
    | _, _ => None
    end
  | e_div e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_int v1), Some (v_int v2) => Some (v_int (v1 / v2)%Z)
    | _, _ => None
    end
  | e_lt e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_int v1), Some (v_int v2) => Some (v_bool (v1 <? v2)%Z)
    | _, _ => None
    end
  | e_eq e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_int v1), Some (v_int v2) => Some (v_bool (v1 =? v2)%Z)
    | Some (v_bool v1), Some (v_bool v2) => Some (v_bool (Bool.eqb v1 v2)%bool)
    | _, _ => None
    end
  | e_and e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_bool v1), Some (v_bool v2) => Some (v_bool (v1 && v2)%bool)
    | _, _ => None
    end
  | e_or e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_bool v1), Some (v_bool v2) => Some (v_bool (v1 || v2)%bool)
    | _, _ => None
    end
  | e_index e1 e2 =>
    match sem_expr m e1, sem_expr m e2 with
    | Some (v_arr t vs), Some (v_int idx) => val_arr_index vs idx
    | Some (v_bag t vs), Some (v_int idx) => val_arr_index vs idx
    | _, _ => None
    end
  | e_length e =>
    match sem_expr m e with
    | Some (v_arr _ vs) => Some (v_int (val_arr_length vs))
    | Some (v_bag _ vs) => Some (v_int (val_arr_length vs))
    | _ => None
    end
  end.

Lemma sem_expr_val_typed : forall env m e v t,
    welltyped_expr env e t
    -> sem_expr m e = Some v
    -> welltyped_memory env m
    -> welltyped_val v t.
Proof.
  intros env m e v t H.
  generalize dependent v.
  generalize dependent m.
  induction H.
  - intros m v Hv.
    simpl in Hv.
    inversion Hv; subst; clear Hv.
    constructor.
  - intros m v Hv Hmem.
    simpl in Hv.
    unfold welltyped_memory in Hmem.
    destruct (Hmem x t H) as [xv [Hxv Ht_xv]].
    apply VarMap.find_1 in Hxv.
    rewrite Hxv in Hv; inversion Hv; subst; clear Hv.
    auto.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H3; subst; clear H3.
      constructor; auto.
      constructor; auto.
    + destruct v0; inversion H3; subst; clear H3.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inversion Hv; subst; clear Hv.
    + destruct v0; destruct v1; inversion H2; subst; clear H2.
      constructor; auto.
    + destruct v0; inversion H2; subst; clear H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      try (solve [inversion Hv|destruct v0; inversion Hv]).
    destruct v0 eqn:Hv0; try (solve [inversion Hv]).
    + Admitted.
(*Qed.*)

Lemma sem_welltyped_expr : forall env m e t,
    welltyped_expr env e t
    -> welltyped_memory env m
    -> exists v, sem_expr m e = Some v.
Proof.
  intros env m e t H.
  generalize dependent m.
  induction H.
  - intros m Hmem; exists (v_int z); auto.
  - intros m Hmem. unfold welltyped_memory in Hmem.
    apply Hmem in H.
    destruct H as [v [Hx_v Htau_v]].
    exists v; simpl.
    apply VarMap.find_1 in Hx_v; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_int).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_int).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_int (z + z0)%Z); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_int).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_int).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_int (z - z0)%Z); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_int).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_int).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_int (z * z0)%Z); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_int).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_int).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_int (z / z0)%Z); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_int).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_int).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_bool (z <? z0)%Z); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    destruct H1 as [Ht_int | Ht_bool]; subst.
    + assert (welltyped_val v1 t_int).
      { eapply sem_expr_val_typed with (e := e1); eauto. }
      assert (welltyped_val v2 t_int).
      { eapply sem_expr_val_typed with (e := e2); eauto. }
      inversion H1; inversion H2; subst; clear H1; clear H2.
      exists (v_bool (z =? z0)%Z); simpl.
      rewrite Hv1; rewrite Hv2; auto.
    + assert (welltyped_val v1 t_bool).
      { eapply sem_expr_val_typed with (e := e1); eauto. }
      assert (welltyped_val v2 t_bool).
      { eapply sem_expr_val_typed with (e := e2); eauto. }
      inversion H1; inversion H2; subst; clear H1; clear H2.
      exists (v_bool (Bool.eqb b b0)); simpl.
      rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_bool).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_bool).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_bool (b && b0)%bool); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - intros m Hmem.
    destruct (IHwelltyped_expr1 m Hmem) as [v1 Hv1];
      destruct (IHwelltyped_expr2 m Hmem) as [v2 Hv2].
    assert (welltyped_val v1 t_bool).
    { eapply sem_expr_val_typed with (e := e1); eauto. }
    assert (welltyped_val v2 t_bool).
    { eapply sem_expr_val_typed with (e := e2); eauto. }
    inversion H1; inversion H2; subst; clear H1; clear H2.
    exists (v_bool (b || b0)%bool); simpl.
    rewrite Hv1; rewrite Hv2; auto.
  - Admitted.
(*Defined.*)

Lemma IZR_gt_0: forall {z}, (z > 0)%Z -> (IZR z > 0)%R.
Proof.
  intros z Hzgt0.
  apply Z.gt_lt in Hzgt0.
  apply Rlt_gt.
  replace (0%R) with (IZR 0%Z); auto.
  apply IZR_lt; auto.
Qed.

Lemma IZR_Zpos_gt_0 : forall p, (IZR (Zpos p) > 0)%R.
Proof.
  intros p.
  assert ((Z.pos p) > 0)%Z.
  constructor.
  apply IZR_gt_0; auto.
Qed.

Definition step_base_instr (m: memory) (c : base_instr)
  : (distr memory) :=
  match c with
  | bi_assign x e =>
    match sem_expr m e with
    | Some v =>  Munit (VarMap.add x v m)
    | _ => distr0
    end
  | bi_laplace x w e =>
    match sem_expr m e with
    | Some (v_int c) => Mlet (Laplace (IZR (Z.pos w)) (IZR_Zpos_gt_0 w) c)
                             (fun v => Munit (VarMap.add x (v_int v) m))
    | _ => distr0
    end
      (* TODO: Fix this *)
  | _ => distr0
  end.

Fixpoint step_cmd (m: memory) (c: cmd)
  : distr (cmd * memory) :=
  match c with
  | i_skip => Munit (i_skip, m)
  | i_base_instr bi =>
    Mlet (step_base_instr m bi) (fun m => Munit (i_skip, m))
  | i_cond e ct cf =>
    match sem_expr m e with
    | Some (v_bool b) => if b then Munit (ct, m) else Munit (cf, m)
    | _ => distr0
    end
  | i_while e body =>
    match sem_expr m e with
    | Some (v_bool b) => if b then Munit (body ;; c, m)%cmd else Munit (i_skip, m)
    | _ => distr0
    end
  | i_seq i_skip c2 =>
    Munit (c2, m)
  | i_seq c1 c2 =>
    Mlet (step_cmd m c1)
         (fun cm => match cm with
                  | (c1', m) => Munit ((c1' ;; c2)%cmd, m)
                  end
         )

  end.


Ltac absurd := let H := fresh "contra" in intros H; inversion H; subst; clear H.
Ltac destruct_sem_expr m rhs :=
  match goal with
  | [ H1 : welltyped_expr ?env rhs ?t,
      H2 : welltyped_memory ?env m
      |- _
    ] => let H := fresh "H_sem_expr" in
        let vrhs := fresh "v_" rhs in
        let Hvrhs := fresh "H_" vrhs in
        assert (H : exists v, sem_expr m rhs = Some v);
        try (eapply sem_welltyped_expr; eauto);
        try (destruct H as [vrhs Hvrhs])
  | _ => fail "Cannot find welltyped conditions"
  end.
Ltac ty_val v :=
  match goal with
  | [
    H1 : welltyped_expr ?env ?expr ?t,
    H2 : sem_expr ?m ?expr = Some v
    |- _ ] =>
    let H := fresh "H_type_" v in
    assert (H : welltyped_val v t);
    try (apply sem_expr_val_typed
           with (env := env) (m := m) (e := expr);
         auto)
  end.
Ltac simpl_distr_monad := repeat (simpl; unfold star, unit).

(* Well typed commands produces distributions whose support are all welltyped *)
Lemma step_welltyped_cmd_preservation : forall env m c,
    welltyped env c
    -> welltyped_memory env m
    -> range (fun cm => welltyped env (fst cm)
                    /\ welltyped_memory env (snd cm)) (step_cmd m c).
Proof.
  intros env m c H.
  generalize dependent m.
  induction H.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    rewrite <- Hf; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct_sem_expr m rhs.
    rewrite H_v_rhs.
    simpl_distr_monad.
    rewrite <- Hf; auto.
    split; auto.
    simpl.
    ty_val v_rhs.
    apply welltyped_memory_add with (t := t); auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct_sem_expr m center.
    rewrite H_v_center.
    ty_val v_center.
    inversion H_type_v_center; subst; clear H_type_v_center.
    simpl_distr_monad.
    rewrite <- (mu_zero (Laplace (IZR (Z.pos w)) (IZR_Zpos_gt_0 w) z)).
    apply mu_stable_eq.
    intros vz.
    rewrite <- Hf; auto.
    split; simpl; auto.
    apply welltyped_memory_add with (t := t_int); auto.
    constructor.
  - intros m Hmem f Hf.
Admitted.
(*
    simpl_distr_monad.
    destruct_sem_expr m e.
    rewrite H_v_e.
    ty_val v_e.
    inversion H_type_v_e; subst; clear H_type_v_e.
    destruct b;
      simpl_distr_monad;
      rewrite <- Hf; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct_sem_expr m e.
    rewrite H_v_e.
    ty_val v_e.
    inversion H_type_v_e; subst; clear H_type_v_e.
    destruct b;
      simpl_distr_monad;
      rewrite <- Hf; auto.
    split.
    + simpl; constructor; auto.
    + simpl; auto.
  - intros m Hmem.
    simpl_distr_monad.
    destruct (cmd_eqdec c1 i_skip).
    + subst; intros f Hf; simpl_distr_monad.
      rewrite <- Hf; auto.
    + destruct c1;
        try (solve [exfalso; apply n; auto]);
        try (apply Mlet_range_comp; auto);
        try (intros [c' m']; intros [Hc' Hm']; simpl in *; auto);
        try (intros f Hf; simpl_distr_monad;
             rewrite <- Hf; try split; auto;
             simpl; auto).
Qed.*)

Fixpoint step_trans (m: memory) (c: cmd) (n: nat)
  : distr (cmd * memory) :=
  match n with
  | O => Munit (c, m)
  | S n => Mlet (step_trans m c n) (fun cm => step_cmd (snd cm) (fst cm))
  end.

Lemma step_welltyped_trans_preservation : forall env m c n,
    welltyped env c
    -> welltyped_memory env m
    -> range (fun cm => welltyped env (fst cm)
                    /\ welltyped_memory env (snd cm)) (step_trans m c n).
Proof.
  intros env m c n.
  generalize dependent env.
  generalize dependent m.
  generalize dependent c.
  induction n.
  - intros c m env Hc Hm.
    intros f Hf.
    simpl_distr_monad.
    rewrite <- Hf; auto.
  - intros c m env Hc Hm.
    simpl.
    apply Mlet_range_comp; auto.
    intros [c' m']; intros [Hc' Hm'].
    simpl in *.
    apply step_welltyped_cmd_preservation; auto.
Qed.

Definition final (c : cmd) : bool :=
  match c with
  | i_skip => true
  | _ => false
  end.

Definition step_star (m: memory) (c: cmd) (n : nat)
  : distr memory :=
  Mlet (step_trans m c n)
       (fun cm =>
          match cm with
          | (c, m) => if final c then Munit m else distr0
          end).

Lemma step_welltyped_star_preservation : forall env m c n,
    welltyped env c
    -> welltyped_memory env m
    -> range (fun m => welltyped_memory env m) (step_star m c n).
Proof.
  intros env m c n Hc Hm.
  induction n.
  - intros f Hf; simpl_distr_monad.
    inversion Hc; subst; clear Hc; simpl_distr_monad; try reflexivity.
    rewrite <- Hf; auto.
  - unfold step_star.
    intros f Hf.
    simpl_distr_monad.
    assert (H_step_trans : range (fun cm => welltyped env (fst cm)
                                         /\ welltyped_memory env (snd cm))
                                 (step_trans m c n)).
    { apply step_welltyped_trans_preservation; auto. }
    unfold range in H_step_trans.
    rewrite <- H_step_trans; auto.
    intros [c' m']; intros [Hc' Hm'].
    simpl.
    assert (H_step_cmd : range (fun cm => welltyped env (fst cm)
                                       /\ welltyped_memory env (snd cm))
                               (step_cmd m' c')).
    { apply step_welltyped_cmd_preservation; auto. }
    unfold range in H_step_cmd.
    rewrite <- H_step_cmd; auto.
    intros [c'' m'']; intros [Hc'' Hm''].
    simpl in *.
    destruct (final c'');
      simpl_distr_monad; try reflexivity.
    rewrite <- Hf; auto.
Qed.

Hint Unfold step_cmd.
Hint Unfold step_trans.
Hint Unfold step_star.

Lemma step_star_monotonic : forall (c : cmd) (m : memory) (j k: nat),
    (j <= k)%nat
    -> le_distr (step_star m c j) (step_star m c k).
Proof.
  intros c m j k Hjk.
  induction Hjk as [|k Hle IH]; auto.
  - apply le_distr_trans with (m2 := (step_star m c k)); auto.
    intros f.
    simpl_distr_monad.
    apply mu_monotonic.
    unfold fle.
    intros [c' m'].
    destruct (final c') eqn:Hfinal.
    + simpl_distr_monad.
      destruct c'; try (inversion Hfinal; subst; clear Hfinal).
      simpl_distr_monad.
      reflexivity.
    + simpl_distr_monad; unfold Mdistr0; auto.
Qed.

Definition deno (c: cmd) (m: memory) :=
  mu_lub (step_star m c) (step_star_monotonic c m).

Notation "'[[' c ']]'" := (deno c) (at level 65).

Definition lossless (c : cmd) :=
  forall m, mu ([[ c ]] m) (fun _ => 1%U) == 1%U.

End Make.
