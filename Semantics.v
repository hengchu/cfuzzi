Require Export Coq.Reals.Reals.
Require Export Fourier.

Require Export Random.Prelude.
Require Export Random.Prog.
Require Export Random.Ubase.
Require Export Random.Probas.

Require Export VariableDefinitions.
Require Export VarMap.
Require Export Syntax.

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

Definition memory := VarMap.t val.

Reserved Notation "m '[[' e ']]' '//' v" (at level 65, no associativity).
Inductive bigstep_expr : memory -> expr -> val -> Prop :=
| bigstep_expr_lit : forall m z, m [[e_lit z]] // v_int z
| bigstep_expr_var : forall m x v, VarMap.find x m = Some v
                              -> m [[e_var x]] // v
| bigstep_expr_add : forall m e1 e2 z1 z2, m [[e1]] // (v_int z1)
                                      -> m [[e2]] // (v_int z2)
                                      -> m [[e_add e1 e2]] // (v_int (z1 + z2))
| bigstep_expr_minus : forall m e1 e2 z1 z2, m [[e1]] // (v_int z1)
                                        -> m [[e2]] // (v_int z2)
                                        -> m [[e_minus e1 e2]] // (v_int (z1 - z2))
| bigstep_expr_mult : forall m e1 e2 z1 z2, m [[e1]] // (v_int z1)
                                       -> m [[e2]] // (v_int z2)
                                       -> m [[e_mult e1 e2]] // (v_int (z1 * z2))
| bigstep_expr_div : forall m e1 e2 z1 z2, m [[e1]] // (v_int z1)
                                      -> m [[e2]] // (v_int z2)
                                      -> m [[e_div e1 e2]] // (v_int (z1 / z2))
| bigstep_expr_lt : forall m e1 e2 z1 z2, m [[e1]] // (v_int z1)
                                     -> m [[e2]] // (v_int z2)
                                     -> m [[e_lt e1 e2]] // (v_bool (z1 <? z2)%Z)
| bigstep_expr_eq : forall m e1 e2 z1 z2, m [[e1]] // (v_int z1)
                                     -> m [[e2]] // (v_int z2)
                                     -> m [[e_eq e1 e2]] // (v_bool (z1 =? z2)%Z)
| bigstep_expr_and : forall m e1 e2 b1 b2, m [[e1]] // (v_bool b1)
                                      -> m [[e2]] // (v_bool b2)
                                      -> m [[e_and e1 e2]] // (v_bool (b1 && b2))
| bigstep_expr_or : forall m e1 e2 b1 b2, m [[e1]] // (v_bool b1)
                                     -> m [[e2]] // (v_bool b2)
                                     -> m [[e_or e1 e2]] // (v_bool (b1 || b2))
where "m '[[' e ']]' '//' v" := (bigstep_expr m e v).

Lemma IZR_gt_0: forall {z}, (z > 0)%Z -> (IZR z > 0)%R.
Proof.
  intros z Hzgt0.
  apply Z.gt_lt in Hzgt0.
  apply Rlt_gt.
  replace (0%R) with (IZR 0%Z); auto.
  apply IZR_lt; auto.
Qed.

Inductive step_base_instr : memory -> base_instr -> distr memory -> Prop :=
| step_bi_assign : forall x e m ve,
    m [[e]] // ve
    -> step_base_instr m (bi_assign x e) (Munit (VarMap.add x ve m))
| step_bi_laplace : forall x {w} e m z (wgt0 : (w > 0)%Z),
    m [[e]] // (v_int z)
    -> step_base_instr
        m
        (bi_assign x e)
        (Mlet (Laplace (IZR w) (IZR_gt_0 wgt0) z)
              (fun v => Munit (VarMap.add x (v_int v) m))).

Inductive step_instr : memory -> instr -> distr memory -> Prop :=
| step_i_base_isntr : forall m bi m',
    step_base_instr m bi m' -> step_instr m (i_base_instr bi) m'
| step_i_cond_true : forall m e ct cf mt,
    step_cmd (Munit m) ct mt
    -> m [[e]] // (v_bool true)
    -> step_instr m (i_cond e ct cf) mt
| step_i_cond_false: forall m e ct cf mf,
    step_cmd (Munit m) cf mf
    -> m [[e]] // (v_bool false)
    -> step_instr m (i_cond e ct cf) mf
| step_i_while_end : forall m m' e c,
    m [[e]] // (v_bool false)
    -> eq_distr (Munit m) m'
    -> step_instr m (i_while e c) m'
| step_i_while_loop : forall m e c m' m'',
    m [[e]] // (v_bool true)
    -> step_cmd (Munit m) c m'
    -> step_cmd m' [i_while e c] m''
    -> step_instr m (i_while e c) m''
with step_cmd : distr memory -> cmd -> distr memory -> Prop :=
     | step_cmd_nil : forall m, step_cmd m List.nil m
     | step_cmd_cons : forall m i is m' m'',
         step_instr m i m'
         -> step_cmd m' is m''
         -> step_cmd (Munit m) (i :: is) m''.

Hint Constructors bigstep_expr.
Hint Constructors step_base_instr.
Hint Constructors step_instr.
Hint Constructors step_cmd.

Axiom memory_equiv_implies_eq_distr :
  forall (m1 m2 : memory), VarMap_equiv m1 m2 -> eq_distr (Munit m1) (Munit m2).

Example prog1 :=
  [While (e_lt 0%Z x) do [x <- (e_minus x 1%Z)] end].
Example mem1 := VarMap.add x (v_int 1%Z) (VarMap.empty val).
Example mem1' := VarMap.add x (v_int 0%Z) (VarMap.empty val).
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
    unfold VarMap_equiv.
    intros y.
    destruct (string_dec x y); subst; auto.
Qed.
