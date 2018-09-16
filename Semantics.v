Require Export Coq.Reals.Reals.
Require Export Fourier.

Require Export Random.Prelude.
Require Export Random.Prog.
Require Export Random.Ubase.
Require Export Random.Probas.

Require Export VariableDefinitions.
Require Export Syntax.
Require Export Hlist.

Require Export Program.

Module Type Embedding.
Include Universe.

Parameter iR : U -> R.
Parameter iU : R -> U.
Parameter retract_U : forall u:U, (iU (iR u) == u)%U.
Parameter retract_R : forall x:R, (0 <= x <= 1)%R -> iR (iU x) = x.
Parameter iR_le : forall u v:U, (u <= v)%U -> (iR u <= iR v)%R.
 (* iU truncates *)
Parameter iU_le : forall x y:R, (x <= y)%R -> (iU x <= iU y)%U.
Parameter iR_0 : iR 0 = 0%R.
Parameter iR_1 : iR 1%U = 1%R.
Parameter iR_lub : forall (f: nat -> U) (H:has_ub (fun k => iR (f k))),
  iR (lub f) = SeqProp.lub (fun k => iR (f k)) H.
Parameter iR_plus : forall u v:U, iR (u + v)%U = Rmin 1 (iR u + iR v).
Parameter iR_mult : forall u v:U, iR (u * v)%U = (iR u * iR v)%R.
Parameter iR_inv : forall u:U, iR ([1-] u) = (1 - iR u)%R.
End Embedding.

Module Laplace (E: Embedding).

Import E.
Module RP := Rules(E).
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.

Section LaplaceDistr.

  Local Close Scope nat_scope.
  Local Close Scope U_scope.
  Local Open Scope Z_scope.
  Local Open Scope R_scope.

  Variable eps: R.
  Hypothesis eps_pos: (0 < eps)%R.

  Definition f (a b:Z) : R := exp(-eps * Rabs(IZR a - IZR b)).
  Definition delta (a a': Z) := exp(eps * Rabs(IZR a - IZR a')).

  Lemma f_pos : forall a b, (0 <= f a b)%R.
  Proof.
    intros; apply Rlt_le; apply exp_pos.
  Qed.

  Lemma delta_sym : forall a a', delta a a' = delta a' a.
  Proof.
    intros; unfold delta.
    rewrite Rabs_minus_sym; trivial.
  Qed.

  Lemma delta_pos : forall a a', (0 <= delta a a')%R.
  Proof.
    intros; apply Rlt_le; apply exp_pos.
  Qed.

  Lemma f_notnul : forall a, exists b, (0 < f a b)%R.
  Proof.
    intros; exists 0%Z; apply exp_pos.
  Qed.

  Lemma exp_monotonic : forall x y, (x <= y)%R -> (exp x <= exp y)%R.
  Proof.
    intros.
    apply Rle_lt_or_eq_dec in H; destruct H.
    apply Rlt_le; apply exp_increasing; trivial.
    subst; apply Rle_refl.
  Qed.

  Lemma f_diff_bounded : forall a a' x, (f a x <= delta a a' * f a' x)%R.
  Proof.
    intros; unfold f, delta.
    rewrite <-exp_plus.
    replace (IZR a - IZR x) with (IZR a' - IZR x - (IZR a' - IZR a)) by field.
    replace (eps * Rabs (IZR a - IZR a') + - eps * Rabs (IZR a' - IZR x)) with
        (- (eps * (Rabs (IZR a' - IZR x) - Rabs (IZR a - IZR a')))) by field.
    rewrite Ropp_mult_distr_l_reverse, exp_Ropp, exp_Ropp.
    apply Rle_Rinv; [apply exp_pos | apply exp_pos | ].
    apply exp_monotonic.
    apply Rmult_le_compat_l; [fourier | ].
    rewrite (Rabs_minus_sym (IZR a)).
    apply Rabs_triang_inv.
  Qed.

  Definition Laplace : Z -> distr Z.
  Admitted.

  Lemma Laplace_ratio : forall a a' b,
  iR (mu (Laplace a)  (fun k => if Zeq_bool k b then 1%U else 0)%U) <=
  iR (mu (Laplace a') (fun k => if Zeq_bool k b then 1%U else 0)%U) *
  (delta a a').
  Admitted.

  Lemma Laplace_lossless: forall a,
      (mu (Laplace a) (fun k => 1%U) == 1)%U.
  Admitted.

End LaplaceDistr.
End Laplace.

Module Semantics (E : Embedding).

Module LAP := Laplace(E).
Import E.
Import LAP.
Import LAP.RP.
Import LAP.RP.PP.
Import LAP.RP.PP.MP.
Import LAP.RP.PP.MP.UP.

Definition memory (ts : list tau) := hlist tau tau_denote ts.
Definition mem_get {t ts} (m : memory ts) (x : var t ts) : tau_denote t := h_get m x.
Definition mem_set {t ts} (m : memory ts) (x : var t ts) (v : tau_denote t) : memory ts :=
  h_weak_update v m x.

Program Fixpoint sem_expr
        {t : tau}
        {ts : list tau}
        (m : memory ts) (e : expr t ts) : tau_denote t :=
  match e with
  | e_lit _ v => v
  | e_var _ _ x => mem_get m x
  | e_add _ e1 e2 => (sem_expr m e1 + sem_expr m e2)%Z
  | e_minus _ e1 e2 => (sem_expr m e1 - sem_expr m e2)%Z
  | e_mult _ e1 e2 => (sem_expr m e1 * sem_expr m e2)%Z
  | e_div _ e1 e2 => (sem_expr m e1 / sem_expr m e2)%Z
  | e_lt _ e1 e2 => (sem_expr m e1 <? sem_expr m e2)%Z
  | e_eq _ e1 e2 => (sem_expr m e1 =? sem_expr m e2)%Z
  | e_and _ e1 e2 => andb (sem_expr m e1) (sem_expr m e2)
  | e_or _ e1 e2 => orb (sem_expr m e1) (sem_expr m e2)
  end.

Lemma IZR_gt_0: forall {z}, (z > 0)%Z -> (IZR z > 0)%R.
Proof.
  intros z Hzgt0.
  apply Z.gt_lt in Hzgt0.
  apply Rlt_gt.
  replace (0%R) with (IZR 0%Z); auto.
  apply IZR_lt; auto.
Qed.

Definition step_base_instr {ts} (m: memory ts) (c : base_instr ts)
  : distr (memory ts) :=
  match c in base_instr ts' return (memory ts' -> distr (memory ts')) with
  | bi_assign _ _ x e
    => fun m => Munit (mem_set m x (sem_expr m e))
  | bi_laplace _ c x c_gt_0 e
    => fun m => Mlet (Laplace (IZR c) (IZR_gt_0 c_gt_0) (sem_expr m e))
                 (fun v => Munit (mem_set m x v))
  end m.

Definition step_cmd {ts} (m: memory ts) (c: cmd ts)
  : ((cmd ts) * distr (memory ts)).
  destruct c eqn:Hcmd.
  - apply ([]%list, Munit m).
  - destruct i eqn:Hinstr.
    + pose (m' := step_base_instr m b).
      apply (l, m').
    + destruct (sem_expr m e) eqn:Hcond.
      * pose (cs := (l0 ++ l)%list).
        apply (cs, (Munit m)).
      * pose (cs := (l1 ++ l)%list).
        apply (cs, (Munit m)).
    + destruct (sem_expr m e) eqn:Hguard.
      * pose (cs := (l0 ++ c)%list).
        apply (cs, (Munit m)).
      * apply (l, (Munit m)).
Defined.

Definition step_cmd_lifted {ts} (m : distr (memory ts)) (c : cmd ts)
  : ((cmd ts) * distr (memory ts)).

Fixpoint step_trans {ts} (m: memory ts) (c: cmd ts) (n : nat)
  : ((cmd ts) * distr (memory ts)) :=
  match n with
  | O => (c, Munit m)
  | S n' => match step_trans m c n' with
           | (c', m') => step_cmd m

Example x : var t_int ([t_int]%list)  := m_first t_int List.nil.
Example prog1 :=
  [ While (e_lt (e_lit 0%Z) (e_var x)) do [x <- (e_minus (e_var x) (e_lit 1%Z))] end ]%list.
Example mem1 := @h_cons tau tau_denote t_int []%list 1%Z h_nil.
Example mem1' := @h_cons tau tau_denote t_int []%list 0%Z h_nil.

Example step_prog1:
  exists m_final,
    step_cmd (Munit mem1) prog1 m_final /\ eq_distr (Munit mem1') m_final.
Proof.
  eexists; split.
  - unfold prog1.
    eapply step_cmd_cons; eauto.
    eapply step_i_while_loop.
    assert (mem1 [[x]] // (v_int 1)). {
      unfold mem1; constructor; auto.
    }
    assert (mem1 [[e_lit 0]] // (v_int 0)). {
      constructor.
    }
    replace true with (0 <? 1)%Z; auto.
    eapply step_cmd_cons; eauto.
    constructor; constructor.
    assert (mem1 [[x]] // (v_int 1)). {
      unfold mem1; constructor; auto.
    }
    assert (mem1 [[1%Z]] // (v_int 1)). {
      constructor.
    }
    eapply bigstep_expr_minus; eauto.
    simpl.
    econstructor; eauto.
    apply step_i_while_end; auto.
    pose (mem2 := VarMap.add x (v_int 0%Z) mem1).
    assert (mem2 [[x]] // 0%Z). {
      constructor; auto.
    }
    assert (mem2 [[0%Z]] // 0%Z). {
      auto.
    }
    replace false with (0 <? 0)%Z; auto.
  - apply memory_equiv_implies_eq_distr.
    unfold VarMap.Equiv.
    split.
    + intros y.
      destruct (string_dec x y); subst; split; auto.
    + intros y e1 e2 Hmaps1 Hmaps2.
      apply VarMap.find_1 in Hmaps1.
      apply VarMap.find_1 in Hmaps2.
      unfold find in *; simpl in *.
      destruct (VarDec.eq_dec y x); subst.
      inversion Hmaps1; inversion Hmaps2; subst; auto.
      inversion Hmaps1.
Qed.

End Semantics.
