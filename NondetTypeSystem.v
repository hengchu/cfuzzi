Require Export Cfuzzi.Pattern.
Require Export Cfuzzi.TypeSystem.
Require Import Coq.Reals.Reals.
Require Export Coq.QArith.QArith.
Require Export Coq.QArith.Qminmax.
Require Import Fourier.

Definition M_nondet (A : Type) :=
  list A.

Definition M_nondet_return {A: Type} (a : A) : M_nondet A :=
  [a].

Definition M_nondet_bind {A B: Type} (ma: M_nondet A) (f: A -> M_nondet B): M_nondet B :=
  List.concat (List.map f ma).

Lemma List_Forall_app: forall {A} (P : A -> Prop) xs ys,
    Forall P xs -> Forall P ys -> Forall P (xs ++ ys).
Proof.
  intros A P xs ys HForall.
  induction HForall.
  - intros Hys. simpl. auto.
  - intros Hys. simpl. constructor; auto.
Qed.

Lemma List_Forall_concat: forall {A} (P : A -> Prop) xs,
    Forall (fun x => Forall P x) xs -> Forall P (concat xs).
Proof.
  intros A P xs HForall.
  induction HForall.
  - simpl. constructor.
  - simpl. apply List_Forall_app; auto.
Qed.

Lemma List_Forall_concatMap: forall {A B: Type} (P: A -> Prop) (Q: B -> Prop) (xs: list A)
                               (f: A -> list B),
    (forall a, P a -> Forall Q (f a))
    -> Forall P xs
    -> Forall Q (List.concat (List.map f xs)).
Proof.
  intros A B P Q xs f Himpl Hxs.
  induction Hxs.
  - simpl. constructor.
  - simpl. apply List_Forall_app; auto.
Qed.

Notation "x '<--' ma ';;;' b" := (M_nondet_bind ma (fun x => b))
                                   (at level 75, right associativity) : M_nondet_scope.

Bind Scope M_nondet_scope with M_nondet.
Delimit Scope M_nondet_scope with M_nondet.

Definition M_option_bind {A B: Type} (ma: option A) (f: A -> option B): option B :=
  match ma with
  | Some a => f a
  | None => None
  end.

Notation "x '<--' ma ';;;' b" := (M_option_bind ma (fun x => b))
                                 (at level 75, right associativity) : M_option_scope.

Bind Scope M_option_scope with option.
Delimit Scope M_option_scope with option.

Eval compute in (
                 a <-- [ 1;  2;  3]%Z ;;;
                   b <-- [ 5;  6;  7]%Z ;;;
                   M_nondet_return (a, b)
               )%M_nondet.

Module NondetTS
       (E: Embedding)
       (Lap : Laplace E)
       (LOGIC: APRHL E Lap).

Module TSImpl := TS E Lap LOGIC.
Import TSImpl APRHLImpl SEMImpl LAPImpl CARImpl RP PP MP UP EImpl.

(* A typing rule is a pattern to match against, and a function that goes from
   the matched components, a typing environment to the output typing environment
   with potential failure. Since we don't allow strong updates, the simple types
   will not change, and the typing functions don't need to return them *)
Record env_eps :=
  Build_env_eps
    { sensitivities: env;
    epsilon: Q }.
Definition typing_rule_func := uni_env -> env -> st_env -> option (M_nondet env_eps).
Definition typing_rule := (cmd_pat * typing_rule_func)%type.
Definition typing_rule_sound (rule: typing_rule) :=
  forall c uenv senv env envs,
    cmd_pat_matches uenv (fst rule) c
    -> (snd rule) uenv senv env = Some envs
    -> Forall
        (fun e => env ⊕ env |- c ~_(Qreals.Q2R (epsilon e)) c
               : denote_env senv ==> denote_env (sensitivities e))%triple envs.

(* Step returns the resulting typing environment in a non-deterministic monad *)
Fixpoint step (rules: list typing_rule) (prog: cmd)
  : uni_env -> env -> st_env  -> M_nondet (env_eps * (option cmd))%type :=
  fun uenv senv stenv =>
  match rules with
  | [] => []
  | ((cpat, f) :: rules) =>
    match match_cmd_prefix cpat prog uenv with
    | inl _ => []
    | inr (uenv', rem) =>
      match f uenv' senv stenv with
      | None => []
      | Some many_env' =>
        (env' <-- many_env' ;;;
         M_nondet_return (env', rem))%M_nondet
      end
    end ++ (step rules prog uenv senv stenv)
  end.

(* Non-deterministically search for all typing trees up to the given depth *)
Fixpoint search (rules: list typing_rule) (prog: cmd) (depth: nat)
  : uni_env -> env -> st_env -> M_nondet (env_eps * option cmd)%type :=
  fun uenv senv stenv =>
  match depth with
  | O => []
  | S n' =>
    (
      uenv_senv_rem <-- step rules prog uenv senv stenv ;;;
      match uenv_senv_rem with
      | (senv', None) => M_nondet_return (senv', None)
      (* Use the original unification environment so we can re-use unification
         variables across typing rules
       *)
      | (senv', Some rem) => search rules rem n' uenv (sensitivities senv') stenv
      end
    )%M_nondet
  end.

Definition if_sensitive {A: Type} (senv: env) (tenv: st_env) (e: expr) (k : option A) : option A :=
  match sens_expr senv tenv e with
  | None => None
  | Some s => if (s >? 0)%Z then k else None
  end.

Local Open Scope string_scope.

Definition assign_pat :=
  ("?x" <- "?e")%pat.
Definition assign_func : typing_rule_func :=
  fun uenv senv stenv =>
    (x_ur <-- BaseDefinitions.VarMap.find "?x" uenv ;;;
     v <-- try_get_variable x_ur ;;;
     e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     rhs <-- try_get_expr e_ur ;;;
     if welltyped_cmd_compute stenv (v <- rhs)%cmd
     then
       let srhs := sens_expr senv stenv rhs in
       Some [Build_env_eps (env_update v senv srhs) 0%Q]
     else
       None
    )%option.
Definition assign_rule := (assign_pat, assign_func).

Arguments welltyped_cmd_compute : simpl never.
Arguments sens_expr : simpl never.

Lemma assign_rule_sound:
  typing_rule_sound assign_rule.
Proof.
  unfold typing_rule_sound, assign_rule; simpl.
  intros c uenv senv stenv envs Hmatch Henvs.
  unfold assign_pat, assign_func in *.
  inv Hmatch. inv H1. inv H3. inv H5.
  apply VarMap.find_1 in H1.
  apply VarMap.find_1 in H2.
  unfold M_option_bind in Henvs.
  replace (VarMap.find "?x" uenv) with (Some (uni_variable v)) in Henvs; auto.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e)) in Henvs; auto.
  simpl in Henvs.
  destruct (welltyped_cmd_compute stenv (v <- e)%cmd) eqn:Hwelltyped;
    try (simpl in Henvs; solve [inv Henvs] ).
  rewrite <- welltyped_iff in Hwelltyped.
  inv Henvs.
  apply Forall_cons; auto.
  simpl.
  rewrite RMicromega.IQR_0.
  simpl.
  assert (Hwelltyped2: welltyped stenv (v <- e)%cmd) by auto.
  inv Hwelltyped2.
  eapply aprhl_conseq
    with (env1 := stenv)
         (env2 := stenv)
         (Q' := denote_env (env_update v senv (sens_expr senv stenv e))); auto.
  apply aprhl_assign with (env1 := stenv) (env2 := stenv); auto.
  - intros m1 m2 Hm1t Hm2t Hstronger_precond; simpl.
    unfold assign_sub_left, assign_sub_right.
    intros [v2 Hv2]. rewrite Hv2.
    intros [v1 Hv1]. rewrite Hv1.
    unfold mem_set.
    unfold denote_env in *.
    intros x d Hxd.
    destruct (StringDec.eq_dec x v).
    + subst.
      destruct (sens_expr senv stenv e) as [se|] eqn:Hse.
      * simpl in Hxd. unfold env_set in Hxd.
        assert (VarMap.MapsTo v se (VarMap.add v se senv)). {
          apply VarMap.add_1; auto.
        }
        assert (d = se). {
          eapply VarMap_MapsTo_Uniq; eauto.
        }
        subst.
        assert (exists dv, val_metric_f v1 v2 = Some dv /\ (dv <= se)%Z). {
          apply sens_expr_sound
            with (m1 := m1)
                 (m2 := m2)
                 (ctx := senv)
                 (tctx := stenv)
                 (e := e)
                 (t := t); auto.
        }
        destruct H0 as [d' [ Hv1v2 Hd'] ].
        exists v1, v2, d'.
        repeat split; auto.
        apply VarMap.add_1; auto.
        apply VarMap.add_1; auto.
      * simpl in Hxd. unfold env_del in Hxd.
        apply VarMap_MapsTo_remove_False in Hxd. inv Hxd.
    + assert (VarMap.MapsTo x d senv). {
        destruct (sens_expr senv stenv e) as [se|] eqn:Hse; simpl in Hxd.
        - unfold env_set in Hxd. apply VarMap.add_3 with (x := v) (e' := se); auto.
        - unfold env_del in Hxd. apply VarMap.remove_3 with (x := v); auto.
      }
      clear Hxd.
      destruct (Hstronger_precond x d) as [v1' [v2' [vd [Hv1' [Hv2' [Hv1v2 Hvd] ] ] ] ] ]; auto.
      exists v1', v2', vd. repeat split; auto.
      apply VarMap.add_2; auto.
      apply VarMap.add_2; auto.
  - fourier.
Qed.

Definition skip_pat :=
  (cpat_skip)%pat.
Definition skip_func : typing_rule_func :=
  fun uenv senv stenv =>
    Some [Build_env_eps senv 0%Q].
Definition skip_rule := (skip_pat, skip_func).

Lemma skip_rule_sound:
  typing_rule_sound skip_rule.
Proof.
  unfold typing_rule_sound, skip_rule; simpl.
  intros c uenv senv stenv envs Hmatch Henvs.
  unfold skip_pat, skip_func in *.
  inv Hmatch.
  inv Henvs.
  constructor; auto.
  simpl.
  rewrite RMicromega.IQR_0.
  apply aprhl_skip.
Qed.

Definition cond_sens_pat :=
  (If "?e"
   then "?c1"
   else "?c2"
   end)%pat.
Definition cond_sens_func : typing_rule_func :=
  (fun uenv senv stenv =>
    e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
    e <-- try_get_expr e_ur ;;;
    c1_ur <-- BaseDefinitions.VarMap.find "?c1" uenv ;;;
    c1 <-- try_get_cmd c1_ur ;;;
    c2_ur <-- BaseDefinitions.VarMap.find "?c2" uenv ;;;
    c2 <-- try_get_cmd c2_ur ;;;
    if welltyped_cmd_compute stenv (If e then c1 else c2 end)%cmd
    then
      let modified_vars := VarSet.union (mvs c1) (mvs c2)%list in
      if_sensitive
        senv stenv e
        (Some [Build_env_eps
                 (VarSet.fold (fun x senv => env_update x senv None) modified_vars senv)
                 0%Q]%list)
    else None
  )%option.
Definition cond_sens_rule := (cond_sens_pat, cond_sens_func).

Lemma cond_sens_rule_sound:
  typing_rule_sound cond_sens_rule.
Proof.
  unfold typing_rule_sound, cond_sens_rule; simpl.
  intros c uenv senv stenv envs Hmatches Henvs.
  unfold cond_sens_pat, cond_sens_func in *.
  inv Hmatches. inv Henvs.
  inv H3; inv H5; inv H6.
  apply VarMap.find_1 in H2.
  apply VarMap.find_1 in H3.
  apply VarMap.find_1 in H4.
  unfold M_option_bind in H0.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e)) in H0; auto.
  replace (VarMap.find "?c1" uenv) with (Some (uni_cmd c1)) in H0; auto.
  replace (VarMap.find "?c2" uenv) with (Some (uni_cmd c2)) in H0; auto.
  simpl in H0.
  unfold if_sensitive in H0.
  destruct (sens_expr senv stenv e) as [se|] eqn:Hse;
    destruct (welltyped_cmd_compute stenv (If e then c1 else c2 end)%cmd) eqn:Htyped;
    try (solve [inv H0] ).
  rewrite <- welltyped_iff in Htyped.
  destruct (se >? 0)%Z eqn:H_se_gt_0;
    try (solve [inv H0] ).
  inv H0.
  constructor; auto.
  simpl.
  rewrite RMicromega.IQR_0.
  apply mvs_inf_sound; auto.
Qed.

Definition while_sens_pat :=
  (While "?e" do
         "?c"
   end)%pat.
Definition while_sens_func : typing_rule_func :=
  (fun uenv senv stenv =>
     e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     c_ur <-- BaseDefinitions.VarMap.find "?c" uenv ;;;
     c <-- try_get_cmd c_ur ;;;
     if welltyped_cmd_compute stenv (While e do c end)%cmd
     then
       let modified_vars := mvs c in
       if_sensitive
         senv stenv e
         (Some [Build_env_eps
                  (VarSet.fold (fun x senv => env_update x senv None) modified_vars senv)
                  0%Q]%list)
     else None
  )%option.
Definition while_sens_rule := (while_sens_pat, while_sens_func).

Lemma while_sens_rule_sound:
  typing_rule_sound while_sens_rule.
Proof.
  unfold typing_rule_sound, while_sens_rule; simpl.
  intros c uenv senv stenv envs Hmatches Henvs.
  unfold while_sens_pat, while_sens_func in *.
  inv Hmatches. inv H2; inv H4.
  unfold M_option_bind in *.
  apply VarMap.find_1 in H1. apply VarMap.find_1 in H2.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e)) in Henvs; auto.
  replace (VarMap.find "?c" uenv) with (Some (uni_cmd c0)) in Henvs; auto.
  simpl in Henvs. unfold if_sensitive in Henvs.
  destruct (sens_expr senv stenv e) as [se|] eqn:Hse;
    destruct (welltyped_cmd_compute stenv (While e do c0 end)%cmd) eqn:Htyped;
    try (solve [inv Henvs] ).
  rewrite <- welltyped_iff in Htyped.
  destruct (se >? 0)%Z eqn:Hse_gt_0;
    try (solve [inv Henvs] ).
  inv Henvs.
  constructor; auto.
  simpl.
  rewrite RMicromega.IQR_0.
  replace (mvs c0) with (mvs (While e do c0 end)%cmd); auto.
  apply mvs_inf_sound; auto.
Qed.

Definition if_nonsens_pat :=
  (If "?e"
   then "?c1"
   else "?c2"
   end)%pat.

Definition if_nonsens_func
           (recur: env -> st_env -> cmd -> option (M_nondet env_eps)): typing_rule_func :=
  fun uenv senv stenv =>
    (e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     s_e <-- sens_expr senv stenv e ;;;
     if negb (s_e =? 0)%Z
     then None
     else
       c1_ur <-- BaseDefinitions.VarMap.find "?c1" uenv ;;;
       c1 <-- try_get_cmd c1_ur ;;;
       c2_ur <-- BaseDefinitions.VarMap.find "?c2" uenv ;;;
       c2 <-- try_get_cmd c2_ur ;;;
       if welltyped_cmd_compute stenv (If e then c1 else c2 end)%cmd
       then
         many_senv1 <-- recur senv stenv c1 ;;;
         many_senv2 <-- recur senv stenv c2 ;;;
         Some (
           senv1 <-- many_senv1 ;;;
           senv2 <-- many_senv2 ;;;
            M_nondet_return
                       (Build_env_eps
                          (env_max
                             (sensitivities senv1)
                             (sensitivities senv2))
                          (Qmax (epsilon senv1) (epsilon senv2))%Q))%M_nondet
       else None
    )%option.
Definition if_nonsens_rule (recur: env -> st_env -> cmd -> option (M_nondet env_eps)) :=
  (if_nonsens_pat, if_nonsens_func recur).

Definition recur_sound (f: env -> st_env -> cmd -> option (M_nondet env_eps)) :=
  forall senv stenv c envs,
    f senv stenv c = Some envs
    -> Forall
        (fun r => stenv ⊕ stenv |- c ~_(Qreals.Q2R (epsilon r)) c
                               : denote_env senv ==> denote_env (sensitivities r))%triple
        envs.

Lemma if_nonsens_rule_sound:
  forall f, recur_sound f -> typing_rule_sound (if_nonsens_rule f).
Proof.
  intros recur Hrecur.
  unfold recur_sound, typing_rule_sound, if_nonsens_rule in *.
  intros c uenv senv stenv envs Hmatches Henvs.
  unfold if_nonsens_pat, if_nonsens_func in *.
  simpl in *.
  inv Hmatches. inv H3; inv H5; inv H6.
  apply VarMap.find_1 in H1.
  apply VarMap.find_1 in H2.
  apply VarMap.find_1 in H3.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e)) in Henvs; auto.
  replace (VarMap.find "?c1" uenv) with (Some (uni_cmd c1)) in Henvs; auto.
  replace (VarMap.find "?c2" uenv) with (Some (uni_cmd c2)) in Henvs; auto.
  simpl in Henvs.
  destruct (sens_expr senv stenv e) as [se|] eqn:Hse;
    try (solve [inv Henvs] ).
  simpl in Henvs.
  destruct (se =? 0)%Z eqn:Hse_gt_0;
    try (solve [inv Henvs] ).
  destruct (welltyped_cmd_compute stenv (If e then c1 else c2 end)%cmd) eqn:Htyped;
    try (solve [inv Henvs] ).
  rewrite <- welltyped_iff in Htyped.
  simpl in Henvs.
  remember (recur senv stenv c1) as envs1.
  remember (recur senv stenv c2) as envs2.
  destruct envs1 as [envs1'|] eqn:Henvs1;
    destruct envs2 as [envs2'|] eqn:Henvs2;
    try (solve [inv Henvs] ).
  simpl in Henvs.
  rewrite Z.eqb_eq in Hse_gt_0.
  clear H1 H2 H3; subst.
  inv Henvs.
  eapply List_Forall_concatMap; eauto.
  intros [env1 eps1] Henv1.
  eapply List_Forall_concatMap; eauto.
  intros [env2 eps2] Henv2.
  constructor; auto.
  simpl in *.
  apply aprhl_cond; auto.
  - intros m1 m2 Hm1t Hm2t Hm1m2.
    inv Htyped.
    apply bool_0_same with (senv := senv) (stenv := stenv); auto.
  - inv Htyped; eapply aprhl_conseq; eauto.
    intros m1 m2 Hm1t Hm2t [Hm1m2 Hm1e_true]. auto.
    intros m1 m2 Hm1t Hm2t Hm1m2.
    apply env_max_impl_1; auto.
    apply Qreals.Qle_Rle.
    apply Q.le_max_l.
  - inv Htyped; eapply aprhl_conseq; eauto.
    intros m1 m2 Hm1t Hm2t [Hm1m2 Hm1e_false]. auto.
    intros m1 m2 Hm1t Hm2t Hm1m2.
    apply env_max_impl_2; auto.
    apply Qreals.Qle_Rle.
    apply Q.le_max_r.
Qed.

Definition while_nonsens_pat :=
  (While "?e" do
         "?c"
   end)%pat.
Definition while_nonsens_func (recur: env -> st_env -> cmd -> option (M_nondet env_eps)): typing_rule_func :=
  fun uenv senv stenv =>
    (e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     s_e <-- sens_expr senv stenv e ;;;
     if negb ((s_e =? 0)%Z)
     then None
     else c_ur <-- BaseDefinitions.VarMap.find "?c" uenv ;;;
          c <-- try_get_cmd c_ur ;;;
          if (welltyped_cmd_compute stenv (While e do c end)%cmd)
          then
            many_senv' <-- recur senv stenv c ;;;
            Some (
              senv' <-- many_senv' ;;;
              if (Qeq_bool (epsilon senv') 0%Q)
                && (BaseDefinitions.VarMap.equal Z.eqb senv (sensitivities senv'))
              then M_nondet_return senv'
              else []
            )%M_nondet
          else None
    )%option.

Definition while_nonsens_rule (recur: env -> st_env -> cmd -> option (M_nondet env_eps)) :=
  (while_nonsens_pat, while_nonsens_func recur).

Lemma while_nonsens_rule_sound:
  forall f, recur_sound f
       -> typing_rule_sound (while_nonsens_rule f).
Proof.
  intros recur Hrecur.
  unfold typing_rule_sound.
  intros c uenv senv stenv envs Hmatches.
  unfold while_nonsens_rule in *.
  unfold while_nonsens_pat in *.
  unfold while_nonsens_func in *.
  simpl in *.
  intros Henvs.
  inv Hmatches.
  inv H2; inv H4.
  apply VarMap.find_1 in H1.
  apply VarMap.find_1 in H2.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e)) in Henvs; auto.
  replace (VarMap.find "?c" uenv) with (Some (uni_cmd c0)) in Henvs; auto.
  simpl in Henvs.
  destruct (sens_expr senv stenv e) as [se|] eqn:Hse;
    try (solve [inv Henvs] ).
  simpl in Henvs.
  destruct (se =? 0)%Z eqn:H_se_gt_0;
    try (solve [inv Henvs] ).
  destruct (welltyped_cmd_compute stenv (While e do c0 end)%cmd) eqn:Htyped;
    try (solve [inv Henvs] ).
  rewrite <- welltyped_iff in Htyped.
  destruct (recur senv stenv c0) as [envs1|] eqn:Henvs1;
    try (solve [inv Henvs] ).
  simpl in Henvs.
  inv Henvs.
  eapply List_Forall_concatMap; eauto.
  intros [env1 eps1] Henv1_eps1.
  simpl in *.
  destruct (Qeq_bool eps1 0) eqn:Heps1_eq_0;
    destruct (VarMap.equal Z.eqb senv env1) eqn:Hsenv_eq_env1;
    try (solve [constructor; auto] ).
  simpl.
  constructor; auto.
  simpl.
  rewrite Qeq_bool_iff in Heps1_eq_0.
  apply Qreals.Qeq_eqR in Heps1_eq_0.
  rewrite Heps1_eq_0.
  rewrite RMicromega.IQR_0.
  apply env_equal_Equal in Hsenv_eq_env1.
  assert (VarMap.Equal senv senv) by reflexivity.
  eapply env_equal_inv1; eauto.
  eapply aprhl_conseq
    with (Q' := fun m1 m2 => denote_env senv m1 m2 /\ sem_expr m1 e = Some (v_bool false)); eauto.
  eapply aprhl_while0; auto.
  - intros m1 m2 Hm1m2 Hm1t Hm2t.
    inv Htyped.
    rewrite Z.eqb_eq in H_se_gt_0.
    rewrite H_se_gt_0 in Hse.
    apply bool_0_same with (senv := senv) (stenv := stenv); auto.
  - inv Htyped.
    eapply aprhl_conseq with (P' := denote_env senv); eauto.
    + intros m1 m2 Hm1t Hm2t [Hm1m2 Hm1e]; auto.
    + intros m1 m2 Hm1t Hm2t; apply denote_env_equal_inv; auto.
    + rewrite Heps1_eq_0.
      rewrite RMicromega.IQR_0.
      fourier.
  - intros m1 m2 Hm1t Hm2t [Hm1m2 Hm1e]; auto.
  - fourier.
Qed.

Definition cond_inc_pat :=
  (If "?e"
   then "?x" <- epv "?x" :+ epl "?k1"
   else "?x" <- epv "?x" :+ epl "?k2"
   end)%pat.
Definition cond_inc_func : typing_rule_func :=
  fun uenv senv stenv =>
    (
      e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
      e <-- try_get_expr e_ur ;;;
      if_sensitive senv stenv e
        (x_ur <-- BaseDefinitions.VarMap.find "?x" uenv ;;;
         x <-- try_get_variable x_ur ;;;
         k1_ur <-- BaseDefinitions.VarMap.find "?k1" uenv ;;;
         k1 <-- try_get_Z k1_ur ;;;
         k2_ur <-- BaseDefinitions.VarMap.find "?k2" uenv ;;;
         k2 <-- try_get_Z k2_ur ;;;
         if welltyped_cmd_compute
              stenv
              (If e then x <- x :+ k1 else x <- x :+ k2 end)%cmd
         then
           let diff := Z.abs (k1 - k2)%Z in
           match BaseDefinitions.VarMap.find x senv with
           | None => Some [Build_env_eps senv 0%Q]
           | Some s => Some [Build_env_eps
                              (env_update x senv (Some (s + diff)%Z))
                              0%Q]
           end
        else None)%option
    )%option.
Definition cond_inc_rule := (cond_inc_pat, cond_inc_func).

Ltac inv_matches :=
  repeat match goal with
         | [ H : cmd_pat_matches ?uenv ?cpat ?c |- _ ]
           => inv H
         | [ H : bi_pat_matches ?uenv ?bipat ?bi |- _ ]
           => inv H
         | [ H : expr_pat_matches ?uenv ?epat ?e |- _ ]
           => inv H
         | [ H : var_pat_matches ?uenv ?vpat ?v |- _ ]
           => inv H
         | [ H : Z_pat_matches ?uenv ?zpat ?z |- _ ]
           => inv H
         end.

Ltac inv_welltyped :=
  match goal with
  | [ H : welltyped ?stenv ?c |- _ ]
    => inv H
  | [ H : welltyped_expr ?stenv ?e ?t |- _ ]
    => inv H
  end.

Ltac collapse_dup_MapsTo :=
  match goal with
  | [ H1 : VarMap.MapsTo ?x ?e1 ?m,
      H2 : VarMap.MapsTo ?x ?e2 ?m
      |- _ ]
    => let H := fresh H1 "_eq_" H2 in
      assert (H : e1 = e2) by
          (eapply VarMap_MapsTo_Uniq; eauto)
  end.

Lemma cond_inc_rule_sound:
  typing_rule_sound cond_inc_rule.
Proof.
  unfold typing_rule_sound.
  intros c uenv senv stenv envs Hmatches Henvs.
  unfold cond_inc_rule in *; simpl in *.
  unfold cond_inc_pat, cond_inc_func in *.
  simpl in *.
  inv_matches.
  collapse_dup_MapsTo. inv H6_eq_H4. clear H4.
  collapse_dup_MapsTo. inv H7_eq_H6. clear H6.
  collapse_dup_MapsTo. inv H3_eq_H7. clear H7.
  apply VarMap.find_1 in H8.
  apply VarMap.find_1 in H3.
  apply VarMap.find_1 in H5.
  apply VarMap.find_1 in H2.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e)) in Henvs; auto.
  replace (VarMap.find "?x" uenv) with (Some (uni_variable v)) in Henvs; auto.
  replace (VarMap.find "?k1" uenv) with (Some (uni_Z z0)) in Henvs; auto.
  replace (VarMap.find "?k2" uenv) with (Some (uni_Z z)) in Henvs; auto.
  simpl in Henvs.
  unfold if_sensitive in Henvs.
  destruct (sens_expr senv stenv e) as [se|] eqn:Hse;
    try (solve [inv Henvs] ).
  destruct (se >? 0)%Z eqn:Hse_gt_0;
    try (solve [inv Henvs] ).
  destruct (welltyped_cmd_compute
              stenv
              (If e then (v <- v :+ z0) else (v <- v :+ z) end)%cmd)
           eqn:Htyped;
    try (solve [inv Henvs] ).
  rewrite <- welltyped_iff in Htyped.
  destruct (VarMap.find v senv) eqn:HMapsTo_v_senv.
  + apply VarMap.find_2 in HMapsTo_v_senv.
    inv Henvs. clear H8 H3 H5 H2.
    constructor; auto.
    simpl.
    rewrite RMicromega.IQR_0.
    inv Htyped.
    apply aprhl_cond_L; auto.
    * apply aprhl_cond_R; auto.
      ** eapply aprhl_conseq; eauto.
         apply aprhl_assign; auto.
         *** intros m1 m2 Hm1t Hm2t Hm1m2.
             destruct Hm1m2 as [ [Hm1m2 Hm1e] Hm2e].
             simpl. unfold env_set, assign_sub_left, assign_sub_right.
             intros [v2 Hv2]. rewrite Hv2.
             intros [v1 Hv1]. rewrite Hv1.
             unfold denote_env in *.
             intros x d Hxd.
             simpl in Hv1, Hv2.
             destruct (VarMap.find v m2) as [v2'|] eqn:Hv2';
               destruct (VarMap.find v m1) as [v1'|] eqn:Hv1';
               try (solve [inv Hv2|inv Hv1] ).
             inv H4; inv H5. inv H6; inv H7. clear H6.
             apply VarMap.find_2 in Hv1'.
             apply VarMap.find_2 in Hv2'.
             assert (welltyped_val v1' t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m1) (x := v); auto. }
             assert (welltyped_val v2' t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m2) (x := v); auto. }
             inv H; inv H0. inv Hv1; inv Hv2.
             destruct (StringDec.eq_dec x v).
             **** subst.
                  assert (VarMap.MapsTo
                            v
                            (z1 + Z.abs (z0 - z))%Z
                            (VarMap.add v (z1 + Z.abs (z0 - z))%Z senv)).
                  { apply VarMap.add_1; auto. }
                  collapse_dup_MapsTo; subst. clear H.
                  exists (z2 + z0)%Z, (z3 + z0)%Z, (Z.abs ((z2 + z0) - (z3 + z0)))%Z.
                  unfold mem_set.
                  repeat split; try (solve [apply VarMap.add_1; auto] ).
                  assert (z2 + z0 - (z3 + z0) = z2 - z3)%Z.
                  { omega. }
                  rewrite H.
                  assert (Z.abs (z2 - z3) <= z1)%Z.
                  {
                    destruct (Hm1m2 v z1) as [z1' [z2' [zd [Hz1' [Hz2' [Hz1z2' Hzd] ] ] ] ] ]; auto.
                    simpl in Hz1z2'.
                    collapse_dup_MapsTo. subst. clear Hz2'.
                    collapse_dup_MapsTo. subst. clear Hz1'.
                    simpl in Hz1z2'. inv Hz1z2'; auto.
                  }
                  assert (0 <= Z.abs (z0 - z))%Z.
                  {
                    apply Z.abs_nonneg.
                  }
                  omega.
             **** apply VarMap.add_3 in Hxd; auto.
                  destruct (Hm1m2 x d)
                    as [xv1 [xv2 [xvd [Hxv1 [Hxv2 [Hxv1xv2 Hxvd] ] ] ] ] ]; auto.
                  exists xv1, xv2, xvd.
                  unfold mem_set.
                  repeat split; try (solve [apply VarMap.add_2; auto] ); auto.
         *** fourier.
      ** eapply aprhl_conseq; eauto.
         apply aprhl_assign; auto.
         *** intros m1 m2 Hm1t Hm2t [ [Hm1m2 Huseless1] Huseless2].
             clear Huseless1 Huseless2.
             simpl.
             unfold denote_env, env_set, assign_sub_left, assign_sub_right in *.
             intros [v2 Hv2]. rewrite Hv2.
             intros [v1 Hv1]. rewrite Hv1.
             intros x d Hxd.
             simpl in Hv1, Hv2.
             destruct (VarMap.find v m2) as [m2v|] eqn:Hm2v;
               destruct (VarMap.find v m1) as [m1v|] eqn:Hm1v;
               try (solve [inv Hv1 | inv Hv2] ).
             inv H4. inv H6.
             apply VarMap.find_2 in Hm1v.
             apply VarMap.find_2 in Hm2v.
             assert (Hm1v_int: welltyped_val m1v t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m1) (x := v); auto. }
             assert (Hm2v_int: welltyped_val m2v t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m2) (x := v); auto. }
             inv Hm1v_int; inv Hm2v_int.
             inv Hv2; inv Hv1.
             destruct (StringDec.eq_dec x v).
             **** subst.
                  remember (z1 + Z.abs (z0 - z))%Z as dist.
                  assert (VarMap.MapsTo v dist (VarMap.add v dist senv)).
                  { apply VarMap.add_1; auto. }
                  assert (d = dist).
                  { collapse_dup_MapsTo; auto. }
                  subst. clear H.
                  exists (z2 + z0)%Z, (z3 + z)%Z, (Z.abs ((z2 + z0) - (z3 + z)))%Z.
                  unfold mem_set.
                  repeat split; try solve [apply VarMap.add_1; auto].
                  assert (z2 + z0 - (z3 + z) = (z2 - z3) + (z0 - z))%Z by omega.
                  rewrite H. clear H.
                  apply Z.le_trans with (m := (Z.abs (z2 - z3) + Z.abs (z0 - z))%Z); auto.
                  apply Z.abs_triangle.
                  assert (Z.abs (z2 - z3) <= z1)%Z.
                  {
                    destruct (Hm1m2 v z1) as [vv1 [vv2 [vvd [Hvv1 [Hvv2 [Hvv1vv2 Hvvd] ] ] ] ] ]; auto.
                    collapse_dup_MapsTo. subst. clear Hvv2.
                    collapse_dup_MapsTo. subst. clear Hvv1.
                    simpl in Hvv1vv2. inv Hvv1vv2. auto.
                  }
                  omega.
             **** apply VarMap.add_3 in Hxd; auto.
                  destruct (Hm1m2 x d)
                    as [xv1 [xv2 [xvd [Hxv1 [Hxv2 [Hxv1xv2 Hxvd] ] ] ] ] ]; auto.
                  exists xv1, xv2, xvd.
                  unfold mem_set.
                  repeat split;
                    try solve [apply VarMap.add_2; auto]; auto.
         *** fourier.
    * apply aprhl_cond_R; auto.
      ** eapply aprhl_conseq; eauto.
         apply aprhl_assign; auto.
         *** intros m1 m2 Hm1t Hm2t [ [Hm1m2 Huseless1] Huseless2].
             clear Huseless1 Huseless2.
             simpl.
             unfold denote_env, env_set, assign_sub_left, assign_sub_right in *.
             intros [v2 Hv2]. rewrite Hv2.
             intros [v1 Hv1]. rewrite Hv1.
             intros x d Hxd.
             simpl in Hv1, Hv2.
             destruct (VarMap.find v m2) as [m2v|] eqn:Hm2v;
               destruct (VarMap.find v m1) as [m1v|] eqn:Hm1v;
               try (solve [inv Hv1 | inv Hv2] ).
             inv H4. inv H6.
             apply VarMap.find_2 in Hm1v.
             apply VarMap.find_2 in Hm2v.
             assert (Hm1v_int: welltyped_val m1v t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m1) (x := v); auto. }
             assert (Hm2v_int: welltyped_val m2v t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m2) (x := v); auto. }
             inv Hm1v_int; inv Hm2v_int.
             inv Hv2; inv Hv1.
             destruct (StringDec.eq_dec x v).
             **** subst.
                  remember (z1 + Z.abs (z0 - z))%Z as dist.
                  assert (VarMap.MapsTo v dist (VarMap.add v dist senv)).
                  { apply VarMap.add_1; auto. }
                  assert (d = dist).
                  { collapse_dup_MapsTo; auto. }
                  subst. clear H.
                  exists (z2 + z)%Z, (z3 + z0)%Z, (Z.abs ((z2 + z) - (z3 + z0)))%Z.
                  unfold mem_set.
                  repeat split; try solve [apply VarMap.add_1; auto].
                  assert (z2 + z - (z3 + z0) = (z2 - z3) + (z - z0))%Z by omega.
                  rewrite H. clear H.
                  apply Z.le_trans with (m := (Z.abs (z2 - z3) + Z.abs (z - z0))%Z); auto.
                  apply Z.abs_triangle.
                  assert (Z.abs (z2 - z3) <= z1)%Z.
                  {
                    destruct (Hm1m2 v z1) as [vv1 [vv2 [vvd [Hvv1 [Hvv2 [Hvv1vv2 Hvvd] ] ] ] ] ]; auto.
                    collapse_dup_MapsTo. subst. clear Hvv2.
                    collapse_dup_MapsTo. subst. clear Hvv1.
                    simpl in Hvv1vv2. inv Hvv1vv2. auto.
                  }
                  assert (z - z0 = -z0 + z)%Z by omega.
                  assert (-z0 + z = - (z0 - z))%Z by omega.
                  rewrite H0; rewrite H1. clear H0 H1.
                  rewrite Z.abs_opp.
                  omega.
             **** apply VarMap.add_3 in Hxd; auto.
                  destruct (Hm1m2 x d)
                    as [xv1 [xv2 [xvd [Hxv1 [Hxv2 [Hxv1xv2 Hxvd] ] ] ] ] ]; auto.
                  exists xv1, xv2, xvd.
                  unfold mem_set.
                  repeat split;
                    try solve [apply VarMap.add_2; auto]; auto.
         *** fourier.
      ** eapply aprhl_conseq; eauto.
         apply aprhl_assign; auto.
         *** intros m1 m2 Hm1t Hm2t Hm1m2.
             destruct Hm1m2 as [ [Hm1m2 Hm1e] Hm2e].
             simpl. unfold env_set, assign_sub_left, assign_sub_right.
             intros [v2 Hv2]. rewrite Hv2.
             intros [v1 Hv1]. rewrite Hv1.
             unfold denote_env in *.
             intros x d Hxd.
             simpl in Hv1, Hv2.
             destruct (VarMap.find v m2) as [v2'|] eqn:Hv2';
               destruct (VarMap.find v m1) as [v1'|] eqn:Hv1';
               try (solve [inv Hv2|inv Hv1] ).
             inv H4; inv H5. inv H6; inv H7. clear H6.
             apply VarMap.find_2 in Hv1'.
             apply VarMap.find_2 in Hv2'.
             assert (welltyped_val v1' t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m1) (x := v); auto. }
             assert (welltyped_val v2' t_int).
             { apply welltyped_memory_val with (env := stenv) (m := m2) (x := v); auto. }
             inv H; inv H0. inv Hv1; inv Hv2.
             destruct (StringDec.eq_dec x v).
             **** subst.
                  assert (VarMap.MapsTo
                            v
                            (z1 + Z.abs (z0 - z))%Z
                            (VarMap.add v (z1 + Z.abs (z0 - z))%Z senv)).
                  { apply VarMap.add_1; auto. }
                  collapse_dup_MapsTo; subst. clear H.
                  exists (z2 + z)%Z, (z3 + z)%Z, (Z.abs ((z2 + z) - (z3 + z)))%Z.
                  unfold mem_set.
                  repeat split; try (solve [apply VarMap.add_1; auto] ).
                  assert (z2 + z - (z3 + z) = z2 - z3)%Z by omega.
                  rewrite H. clear H.
                  assert (Z.abs (z2 - z3) <= z1)%Z.
                  {
                    destruct (Hm1m2 v z1) as [z1' [z2' [zd [Hz1' [Hz2' [Hz1z2' Hzd] ] ] ] ] ]; auto.
                    simpl in Hz1z2'.
                    collapse_dup_MapsTo. subst. clear Hz2'.
                    collapse_dup_MapsTo. subst. clear Hz1'.
                    simpl in Hz1z2'. inv Hz1z2'; auto.
                  }
                  assert (0 <= Z.abs (z0 - z))%Z.
                  {
                    apply Z.abs_nonneg.
                  }
                  omega.
             **** apply VarMap.add_3 in Hxd; auto.
                  destruct (Hm1m2 x d)
                    as [xv1 [xv2 [xvd [Hxv1 [Hxv2 [Hxv1xv2 Hxvd] ] ] ] ] ]; auto.
                  exists xv1, xv2, xvd.
                  unfold mem_set.
                  repeat split; try (solve [apply VarMap.add_2; auto] ); auto.
         *** fourier.
  + inv Henvs.
    constructor; auto.
    simpl.
    rewrite RMicromega.IQR_0.
    eapply aprhl_conseq; auto.
    apply mvs_inf_sound; auto.
    * intros m1 m2 Hm1t Hm2t Hm1m2. apply Hm1m2.
    * intros m1 m2 Hm1t Hm2t Hm1m2.
      simpl in Hm1m2. unfold env_del in Hm1m2.
      assert (VarMap.Equal senv (VarMap.remove v senv)).
      {
        rewrite VarMap_remove_same; auto.
        reflexivity.
      }
      rewrite denote_env_equal_inv.
      apply Hm1m2.
      rewrite VarSet.fold_1.
      simpl. unfold Basics.flip. simpl.
      destruct (VarSet.MF.eq_dec v v) as [Hvv|Hvv];
        try (solve [exfalso; apply Hvv; auto] ).
      simpl.
      auto.
    * fourier.
Qed.

Definition simple_arr_map_pat :=
  ("?idx" <- 0%Z ;;
   len("?arr_out") <- len(epv "?arr_in") ;;
   While (epv "?idx") :< len(epv "?arr_in") do
     "?t" <- (epv "?arr_in") !! (epv "?idx") ;;
     at("?arr_out", epv "?idx") <- "?e" ;;
     "?idx" <- epv "?idx" :+ epl 1%Z
   end
  )%pat.

Arguments lossless_compute : simpl never.

Definition guard {P Q} (b : {P} + {Q}) : option Datatypes.unit :=
  if b then Some tt else None.

Definition guardb (b: bool): option Datatypes.unit :=
  if b then Some tt else None.

Definition var_neqdec (v1 v2: var) : {v1 <> v2} + {v1 = v2}
  := Sumbool.sumbool_not (v1 = v2) (v1 <> v2) (var_eqdec v1 v2).

Definition simple_arr_map_func: typing_rule_func :=
  fun uenv senv stenv =>
    (idx_ur <-- BaseDefinitions.VarMap.find "?idx" uenv ;;;
     idx <-- try_get_variable idx_ur ;;;
     s_idx <-- BaseDefinitions.VarMap.find idx senv ;;;
     if (negb (s_idx =? 0))%Z
     then None
     else (
         t_ur <-- BaseDefinitions.VarMap.find "?t" uenv ;;;
         t <-- try_get_variable t_ur ;;;
         e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
         e <-- try_get_expr e_ur ;;;
         _ <-- guardb (lossless_compute e) ;;;
         if VarSet.equal (fvs e) (VarSet.singleton t)
         then
           arr_in_ur <-- BaseDefinitions.VarMap.find "?arr_in" uenv ;;;
           arr_in <-- try_get_variable arr_in_ur ;;;
           t_arr_in <-- VarMap.find arr_in stenv ;;;
           _ <-- guardb (is_array t_arr_in) ;;;
           arr_out_ur <-- BaseDefinitions.VarMap.find "?arr_out" uenv ;;;
           arr_out <-- try_get_variable arr_out_ur ;;;
           t_arr_out <-- VarMap.find arr_out stenv ;;;
           _ <-- guardb (is_array t_arr_out) ;;;
           t_e <-- welltyped_expr_compute stenv e ;;;
           _ <-- guardb (match t_arr_out with
                       | t_arr t' => if tau_eqdec t_e t' then true else false
                       | _ => false
                       end) ;;;
           _ <-- guard (var_neqdec arr_in arr_out) ;;;
           let prog := (
                 idx <- 0%Z ;;
                 len(arr_out) <- len(arr_in) ;;
                 While (idx :< len(arr_in))%expr do
                   t <- arr_in !! idx ;;
                   at(arr_out, idx) <- e ;;
                   idx <- idx :+ 1%Z
                 end
               )%cmd in
           _ <-- guardb (welltyped_cmd_compute stenv prog) ;;;
           arr_in_sens <-- env_get arr_in senv ;;;
           s_e <-- sens_expr (env_set t senv 1%Z) stenv e ;;;
           let s_out := lift_option (Z.mul s_e) (env_get arr_in senv) in
           let senv' := env_update t (env_update arr_out senv s_out) s_out in
           Some [Build_env_eps
                   senv'
                   0%Q]
         else
           None
       )%option
    )%option.
Definition simple_arr_map_rule := (simple_arr_map_pat, simple_arr_map_func).

Ltac step_envs e H :=
  let He := fresh in
  destruct e eqn:He;
  try (solve [inv H] );
  simpl in H.

Lemma val_subarr_map_succ:
  forall vs1 vs2 v1 v2 f len,
    M_option_bind
      (val_arr_subarr vs1 len)
      (val_arr_map_option f)
    = val_arr_subarr vs2 len
    -> val_arr_index vs1 len = Some v1
    -> val_arr_index vs2 len = Some v2
    -> Some v2 = f v1
    -> M_option_bind
        (val_arr_subarr vs1 (Z.succ len))
        (val_arr_map_option f)
      = val_arr_subarr vs2 (Z.succ len).
Proof.
  Admitted.

Lemma simple_arr_map_rule_sound:
  typing_rule_sound simple_arr_map_rule.
Proof.
  unfold typing_rule_sound.
  intros c uenv senv stenv envs.
  intros Hmatches Henvs.
  unfold simple_arr_map_rule in *.
  simpl in *.
  unfold simple_arr_map_func, simple_arr_map_pat in *.
  inv_matches.
  collapse_dup_MapsTo. inv H7_eq_H3. clear H3.
  collapse_dup_MapsTo. inv H6_eq_H5. clear H5.
  collapse_dup_MapsTo. inv H13_eq_H7. clear H7.
  collapse_dup_MapsTo. inv H12_eq_H13. clear H13.
  collapse_dup_MapsTo. inv H14_eq_H12. clear H12.
  collapse_dup_MapsTo. inv H16_eq_H14. clear H14.
  collapse_dup_MapsTo. inv H10_eq_H11. clear H11.
  collapse_dup_MapsTo. inv H4_eq_H10. clear H10.
  apply VarMap.find_1 in H2.
  apply VarMap.find_1 in H16.
  apply VarMap.find_1 in H4.
  apply VarMap.find_1 in H6.
  apply VarMap.find_1 in H9.
  replace (VarMap.find "?idx" uenv) with (Some (uni_variable v)) in Henvs; auto.
  replace (VarMap.find "?t" uenv) with (Some (uni_variable v1)) in Henvs; auto.
  replace (VarMap.find "?arr_in" uenv) with (Some (uni_variable v7)) in Henvs; auto.
  replace (VarMap.find "?arr_out" uenv) with (Some (uni_variable v0)) in Henvs; auto.
  replace (VarMap.find "?e" uenv) with (Some (uni_expr e4)) in Henvs; auto.
  simpl in Henvs.
  rename e4 into e.
  rename v into idx.
  rename v7 into arr_in.
  rename v0 into arr_out.
  rename v1 into temp.
  step_envs (VarMap.find idx senv) Henvs.
  step_envs (lossless_compute e) Henvs.
  rename H0 into Hlossless_e.
  step_envs (z =? 0)%Z Henvs.
  step_envs (VarSet.equal (fvs e) (VarSet.singleton temp)) Henvs.
  step_envs (VarMap.find arr_in stenv) Henvs.
  rename t into t_in.
  rename H3 into Ht_arr_in.
  step_envs (is_array t_in) Henvs.
  rename H3 into Ht_in.
  step_envs (VarMap.find arr_out stenv) Henvs.
  rename H3 into Ht_arr_out.
  rename t into t_out.
  step_envs (is_array t_out) Henvs.
  rename H3 into Ht_out.
  step_envs (welltyped_expr_compute stenv e) Henvs.
  rename H3 into Ht_e. rewrite <- welltyped_expr_iff in Ht_e.
  rewrite is_array_prop in Ht_in, Ht_out.
  destruct Ht_in as [t_in' Ht_in']; subst.
  destruct Ht_out as [t_out' Ht_out']; subst.
  step_envs (tau_eqdec t t_out') Henvs.
  clear H3. rename e0 into Ht_eq_t_out'.
  subst.
  step_envs (var_neqdec arr_in arr_out) Henvs.
  clear H3. rename n into Hin_neq_out.
  remember (idx <- 0%Z ;;
            len(arr_out)<- len(arr_in) ;;
            While (idx :< len(arr_in) )%expr do
              (temp <- arr_in !! idx);;
              (at(arr_out, idx)<- e);;
              idx <- idx :+ 1%Z
            end)%cmd as prog.
  step_envs (welltyped_cmd_compute stenv prog) Henvs.
  rename H3 into Htyped.
  step_envs (env_get arr_in senv) Henvs.
  remember (env_set temp senv 1%Z) as senv'.
  step_envs (sens_expr senv' stenv e) Henvs.
  inv Henvs.
  assert (H_arr_in_neq_temp: arr_in <> temp).
  { admit. }
  assert (H_idx_neq_temp: idx <> temp).
  { admit. }
  assert (H_arr_out_neq_temp: arr_out <> temp).
  { admit. }
  assert (Hidx_neq_arr_out: idx <> arr_out).
  { (*TODO*) admit. }
  assert (Hidx_neq_arr_in: idx <> arr_in).
  { admit. }
  constructor; auto.
  simpl.
  rewrite RMicromega.IQR_0.
  replace (0%R) with (0 + 0)%R by (apply Rplus_0_r; auto).
  rewrite <- welltyped_iff in Htyped.
  (* We need to introduce the condition right before eapply conseq because of
  the ordering of variable declaration matters *)
  assert (Hsubset: VarSet.Subset (fvs e) (VarSet.singleton temp)).
  {
    apply VarSet.equal_2 in H1.
    intros a.
    destruct (H1 a).
    apply H7.
  }
  destruct (sem_expr_singleton_fvs)
    with (stenv := stenv) (e := e) (x := temp) (t := t_out') as [f_e Hf_e];
    auto.
  remember (
      (fun m =>
         VarMap.MapsTo idx (v_int 0%Z) m
         /\ VarMap.MapsTo idx (v_int 0%Z) m)) as cond1.
  remember (
      (fun m =>
         exists v_arr_out v_arr_in,
           VarMap.MapsTo arr_out (v_arr t_out' v_arr_out) m
           /\ VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m
           /\ val_arr_length v_arr_out = val_arr_length v_arr_in
    )) as cond2.
  remember (fun m =>
              forall v_idx v_arr_in,
                VarMap.MapsTo idx (v_int v_idx) m
                -> VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m
                -> (0 <= v_idx <= val_arr_length v_arr_in)%Z) as in_bound_cond.
  remember (fun m =>
              forall v_idx v_arr_in,
                VarMap.MapsTo idx (v_int v_idx) m
                -> VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m
                -> (0 <= v_idx < val_arr_length v_arr_in)%Z) as strict_in_bound_cond.
  remember ((fun m1 =>
               forall v_idx v_arr_in v_arr_out,
                 VarMap.MapsTo idx (v_int v_idx) m1
                 -> VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m1
                 -> VarMap.MapsTo arr_out (v_arr t_out' v_arr_out) m1
                 -> M_option_bind
                     (val_arr_subarr v_arr_in v_idx)
                     (val_arr_map_option f_e)
                   = val_arr_subarr v_arr_out v_idx)
           ) as inv.
  remember ((fun m1 =>
               forall v_idx v_arr_in v_arr_out,
                 VarMap.MapsTo idx (v_int v_idx) m1
                 -> VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m1
                 -> VarMap.MapsTo arr_out (v_arr t_out' v_arr_out) m1
                 -> M_option_bind
                     (val_arr_subarr v_arr_in (Z.pred v_idx))
                     (val_arr_map_option f_e)
                   = val_arr_subarr v_arr_out (Z.pred v_idx))
           ) as inv'.
  eapply aprhl_seq; auto;
    try (solve [inv Htyped; auto] ).
  eapply aprhl_conseq;
    try (solve [inv Htyped; auto] ); auto.
  apply aprhl_assign;
    try (solve [inv Htyped; auto] ); auto.
  - (* Instantiate the pre-condition for the while loops *)
    intros m1 m2 Hm1 Hm2 Hm1m2.
    simpl. unfold assign_sub_left, assign_sub_right.
    intros [v_idx2 Hv_idx2]. inv Hv_idx2. simpl.
    intros [v_idx1 Hv_idx1]. inv Hv_idx1. simpl.
    unfold mem_set in *.
    instantiate (1 := fun m1 m2 => cond1 m1 /\ cond1 m2).
    repeat split;
      try (solve [apply VarMap.add_1; auto] ).
  - intros m1 m2 Hm1 Hm2 Hm1m2.
    apply Hm1m2.
  - fourier.
  - replace (0%R) with (0 + 0)%R by (apply Rplus_0_r; auto).
    apply aprhl_seq
      with (Q := fun m1 m2
                 => cond1 m1
                   /\ cond1 m2
                   /\ cond2 m1
                   /\ cond2 m2
                   /\ in_bound_cond m1
                   /\ in_bound_cond m2
                   /\ inv m1
                   /\ inv m2); auto;
      try (solve [do 2 inv_welltyped; auto] ).
    eapply aprhl_conseq;
      try (solve [do 2 inv_welltyped; auto] ).
    apply aprhl_len_assign; auto;
      try (solve [do 2 inv_welltyped; auto] ).
    + intros m1 m2 Hm1 Hm2 Hm1m2.
      unfold assign_len_sub_left, assign_len_sub_right.
      intros [len2 Hlen2]. intros [t2 [arr_out2 Harr_out2] ].
      rewrite Hlen2. rewrite Harr_out2.
      assert (Hlen2_pos: (0 <= len2)%Z).
      {
        simpl in Hlen2.
        destruct (VarMap.find arr_in m2) as [v_arr_in|] eqn:Harr_in;
          try (solve [do 3 inv_welltyped; auto] );
          try (solve [inv Hlen2; auto] ).
        assert (welltyped_val v_arr_in (t_arr t_in')).
        {
          apply VarMap.find_2 in Harr_in.
          apply VarMap.find_2 in Ht_arr_in.
          apply welltyped_memory_val with (env := stenv) (m := m2) (x := arr_in); auto.
        }
        inv H7.
        - inv Hlen2.
          apply val_arr_length_positive with (vs := v_nil); auto.
        - inv Hlen2.
          apply val_arr_length_positive with (vs := (v_cons v vs)); auto.
      }
      assert (Harr2': exists arr2', val_arr_update_length t2 arr_out2 len2 = Some arr2').
      {
        apply val_arr_update_length_pos; auto.
      }
      destruct Harr2' as [arr_out2' Harr_out2'].
      rewrite Harr_out2'.
      intros [len1 Hlen1]. intros [t1 [arr_out1 Harr_out1] ].
      rewrite Hlen1. rewrite Harr_out1.
      assert (Hlen1_pos: (0 <= len1)%Z).
      {
        simpl in Hlen1.
        destruct (VarMap.find arr_in m1) as [v_arr_in|] eqn:Harr_in;
          try (solve [do 3 inv_welltyped; auto|inv Hlen1] ).
        assert (welltyped_val v_arr_in (t_arr t_in')). {
          apply VarMap.find_2 in Harr_in.
          apply VarMap.find_2 in Ht_arr_in.
          apply welltyped_memory_val with (env := stenv) (m := m1) (x := arr_in); auto.
        }
        inv H7.
        - inv Hlen1.
          apply val_arr_length_positive with (vs := v_nil); auto.
        - inv Hlen1.
          apply val_arr_length_positive with (vs := v_cons v vs); auto.
      }
      assert (Harr1': exists arr1', val_arr_update_length t1 arr_out1 len1 = Some arr1').
      {
        apply val_arr_update_length_pos; auto.
      }
      destruct Harr1' as [arr_out1' Harr_out1'].
      rewrite Harr_out1'.
      instantiate
        (1 := fun m1 m2 => cond1 m1
                        /\ cond1 m2
                        /\ cond2 m1
                        /\ cond2 m2
                        /\ in_bound_cond m1
                        /\ in_bound_cond m2
                        /\ inv m1
                        /\ inv m2).
      simpl.
      clear H2 H16 H4 H6 H9.
      unfold mem_set.
      apply VarMap.find_2 in Harr_out1.
      apply VarMap.find_2 in Harr_out2.
      apply VarMap.find_2 in Ht_arr_in.
      apply VarMap.find_2 in Ht_arr_out.
      rewrite Heqcond1 in *; rewrite Heqcond2 in *.
      destruct Hm1m2 as [ [Hidx_m1 _] [Hidx_m2 _] ].
      assert (Ht1_eq_t2: t1 = t2).
      {
        do 2 inv_welltyped.
        inv H9.
        assert (welltyped_val (v_arr t1 arr_out1) (t_arr t)).
        { apply welltyped_memory_val with (env := stenv) (m := m1) (x := arr_out); auto. }
        assert (welltyped_val (v_arr t2 arr_out2) (t_arr t)).
        { apply welltyped_memory_val with (env := stenv) (m := m2) (x := arr_out); auto. }
        inv H2; inv H4; auto.
        apply VarMap.find_1 in H8.
        apply VarMap.find_1 in Ht_arr_out.
        rewrite Ht_arr_out in H8.
        inv H8.
      }
      rewrite Ht1_eq_t2 in *.
      assert (Ht_arr1: welltyped_val (v_arr t2 arr_out1) (t_arr t_out')).
      { apply welltyped_memory_val with (env := stenv) (m := m1) (x := arr_out); auto. }
      assert (Ht_arr2: welltyped_val (v_arr t2 arr_out2) (t_arr t_out')).
      { apply welltyped_memory_val with (env := stenv) (m := m2) (x := arr_out); auto. }
      apply welltyped_arr_elim in Ht_arr1.
      apply welltyped_arr_elim in Ht_arr2.
      destruct Ht_arr1 as [v_arr_out1 Hv_arr_out1];
        destruct Ht_arr2 as [v_arr_out2 Hv_arr_out2].
      simpl in Hlen1, Hlen2.
      destruct (VarMap.find arr_in m1) as [arr_in1|] eqn:Harr_in1;
        try (solve [inv Hlen1] ).
      destruct (VarMap.find arr_in m2) as [arr_in2|] eqn:Harr_in2;
        try (solve [inv Hlen2] ).
      apply VarMap.find_2 in Harr_in1.
      apply VarMap.find_2 in Harr_in2.
      assert (Ht_arr_in1: welltyped_val arr_in1 (t_arr t_in')).
      { apply welltyped_memory_val with (env := stenv) (m := m1) (x := arr_in); auto. }
      assert (Ht_arr_in2: welltyped_val arr_in2 (t_arr t_in')).
      { apply welltyped_memory_val with (env := stenv) (m := m2) (x := arr_in); auto. }
      apply welltyped_arr_elim in Ht_arr_in1.
      apply welltyped_arr_elim in Ht_arr_in2.
      destruct Ht_arr_in1 as [v_arr_in1 Hv_arr_in1];
        destruct Ht_arr_in2 as [v_arr_in2 Hv_arr_in2].
      repeat split; auto;
        try (solve [apply VarMap.add_2; auto] ).
      * inv Hv_arr_out1; inv Hv_arr_out2.
        exists arr_out1', v_arr_in1.
        repeat split; auto;
          try (solve [apply VarMap.add_1; auto|apply VarMap.add_2; auto] ).
        inv Hlen1.
        apply val_arr_update_length_correct with (t := t_out') (vs := v_arr_out1); auto.
      * inv Hv_arr_out1; inv Hv_arr_out2.
        exists arr_out2', v_arr_in2.
        repeat split; auto;
          try (solve [apply VarMap.add_1; auto|apply VarMap.add_2; auto] ).
        inv Hlen2.
        apply val_arr_update_length_correct with (t := t_out') (vs := v_arr_out2); auto.
      * rewrite Heqin_bound_cond.
        intros v_idx v_arr_in Hv_idx Hv_arr_in.
        apply VarMap.add_3 in Hv_idx; auto.
        apply VarMap.find_1 in Hv_idx.
        apply VarMap.find_1 in Hidx_m1.
        rewrite Hidx_m1 in Hv_idx.
        assert (Hlen_pos: (0 <= val_arr_length v_arr_in)%Z).
        {
          apply val_arr_length_positive with (vs := v_arr_in); auto.
        }
        split; inv Hv_idx; try omega.
      * rewrite Heqin_bound_cond.
        intros v_idx v_arr_in Hv_idx Hv_arr_in.
        apply VarMap.add_3 in Hv_idx; auto.
        apply VarMap.find_1 in Hv_idx.
        apply VarMap.find_1 in Hidx_m2.
        rewrite Hidx_m2 in Hv_idx.
        assert (Hlen_pos: (0 <= val_arr_length v_arr_in)%Z).
        {
          apply val_arr_length_positive with (vs := v_arr_in); auto.
        }
        split; inv Hv_idx; try omega.
      * rewrite Heqinv.
        intros v_idx v_arr_in v_arr_out Hv_idx Hv_arr_in Hv_arr_out.
        apply VarMap.add_3 in Hv_idx; auto.
        apply VarMap.add_3 in Hv_arr_in; auto.
        apply VarMap.find_1 in Hv_idx.
        apply VarMap.find_1 in Hv_arr_in.
        apply VarMap.find_1 in Hv_arr_out.
        apply VarMap.find_1 in Hidx_m1.
        rewrite Hidx_m1 in Hv_idx.
        inv Hv_idx.
        rewrite val_arr_subarr0. simpl.
        rewrite val_arr_subarr0. simpl.
        auto.
      * rewrite Heqinv.
        intros v_idx v_arr_in v_arr_out Hv_idx Hv_arr_in Hv_arr_out.
        apply VarMap.add_3 in Hv_idx; auto.
        apply VarMap.add_3 in Hv_arr_in; auto.
        apply VarMap.find_1 in Hv_idx.
        apply VarMap.find_1 in Hv_arr_in.
        apply VarMap.find_1 in Hv_arr_out.
        apply VarMap.find_1 in Hidx_m2.
        rewrite Hidx_m2 in Hv_idx.
        inv Hv_idx.
        rewrite val_arr_subarr0. simpl.
        rewrite val_arr_subarr0. simpl.
        auto.
    + intros ? ? ? ? HQ; apply HQ.
    + fourier.
    + remember ((temp <- arr_in !! idx);;
              (at(arr_out, idx)<- e);;
              idx <- idx :+ 1%Z)%cmd as loopbody.
      remember (
          While (idx :< len(arr_in) )%expr do
                loopbody
          end
        )%cmd as loop.
      apply aprhl_equiv with (c1 := loop) (c1' := (loop ;; i_skip)%cmd)
                             (c2 := loop) (c2' := (i_skip ;; loop)%cmd);
        try (solve [do 2 inv_welltyped; auto] );
        auto.
      replace (0%R) with (0 + 0)%R by (apply Rplus_0_r; auto).
      apply aprhl_seq with (Q := fun m1 m2 => cond2 m1 /\ cond2 m2 /\ in_bound_cond m1 /\ inv m1); auto;
        try (solve [do 2 inv_welltyped; auto] ).
      rewrite Heqloop.
      apply aprhl_conseq
        with (P' := fun m1 m2 => cond2 m1 /\ cond2 m2 /\ in_bound_cond m1 /\ inv m1)
             (Q' := fun m1 m2 => (cond2 m1 /\ cond2 m2 /\ in_bound_cond m1 /\ inv m1) /\
                              sem_expr m1 (idx :< len(arr_in))%expr = Some (v_bool false) )
             (eps' := 0%R);
        try (solve [do 2 inv_welltyped; auto] ).
      apply aprhl_while_L with (P1 := fun m1 => cond2 m1 /\ in_bound_cond m1 /\ inv m1); auto;
        try (solve [do 2 inv_welltyped; auto] ).
      * tauto.
      * (* TODO *) admit.
      * (* Here's the reasoning with the loop body *)
        replace (0%R) with (0 + 0)%R by apply Rplus_0_r.
        apply aprhl_equiv
          with (c1 := loopbody) (c1' := loopbody)
               (c2 := i_skip) (c2' := (i_skip ;; i_skip)%cmd); auto;
          try (solve [do 3 inv_welltyped; auto] ).
        rewrite Heqloopbody.
        remember (fun m =>
                    forall v_idx v_arr_in v,
                      VarMap.MapsTo idx (v_int v_idx) m
                      -> VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m
                      -> val_arr_index v_arr_in v_idx = Some v
                      -> VarMap.MapsTo temp v m) as cond3.
        remember (fun m =>
                    forall v_idx v_arr_in v,
                      VarMap.MapsTo idx (v_int v_idx) m
                      -> VarMap.MapsTo arr_in (v_arr t_in' v_arr_in) m
                      -> val_arr_index v_arr_in (Z.pred v_idx) = Some v
                      -> VarMap.MapsTo temp v m) as cond3'.
        apply aprhl_seq
          with (Q := fun m1 m2 =>
                       cond2 m1
                       /\ cond2 m2
                       /\ cond3 m1
                       /\ strict_in_bound_cond m1
                       /\ inv m1); auto;
          try (solve [do 4 inv_welltyped; auto] ).
        eapply aprhl_conseq; auto;
          try (solve [do 4 inv_welltyped; auto] ).
        apply aprhl_assign_L; auto;
          try (solve [do 4 inv_welltyped; auto] ).
        ** intros m1 m2 Hm1t Hm2t.
           intros [ [Hcond2_m1 [Hcond2_m2 [Hin_bound_m1 Hinv_m1] ] ] Hm1_idx].
           unfold assign_sub_left.
           intros [v_arr_in_idx1 Hv_arr_in_idx1].
           rewrite Hv_arr_in_idx1.
           unfold mem_set.
           instantiate (1 := (fun m1 m2 =>
                                cond2 m1
                                /\ cond2 m2
                                /\ cond3 m1
                                /\ strict_in_bound_cond m1
                                /\ inv m1) : memory_relation).
           simpl.
           repeat split; auto.
           {
             rewrite Heqcond2 in *.
             destruct Hcond2_m1 as [v_arr_out [v_arr_in Hcond2_m1] ].
             exists v_arr_out, v_arr_in.
             destruct Hcond2_m1 as [Helper1 [Helper2 Helper3] ].
             repeat split; try tauto.
             apply VarMap.add_2; auto.
             apply VarMap.add_2; auto.
           }
           {
             rewrite Heqcond3.
             intros v_idx v_arr_in v.
             intros Hv_idx Hv_arr_in Hindex.
             simpl in Hv_arr_in_idx1.
             apply VarMap.add_3 in Hv_arr_in; auto.
             apply VarMap.add_3 in Hv_idx; auto.
             apply VarMap.find_1 in Hv_arr_in.
             apply VarMap.find_1 in Hv_idx.
             rewrite Hv_arr_in in Hv_arr_in_idx1.
             rewrite Hv_idx in Hv_arr_in_idx1.
             rewrite Hindex in Hv_arr_in_idx1.
             inv Hv_arr_in_idx1.
             apply VarMap.add_1; auto.
           }
           {
             rewrite Heqstrict_in_bound_cond.
             intros v_idx v_arr_in Hv_idx Hv_arr_in.
             simpl in Hm1_idx.
             apply VarMap.add_3 in Hv_idx; auto.
             apply VarMap.add_3 in Hv_arr_in; auto.
             rewrite Heqin_bound_cond in Hin_bound_m1.
             split.
             - destruct (Hin_bound_m1 v_idx v_arr_in)
                 as [Hin_bound_m1_prop1 Hin_bound_m1_prop2]; auto.
             - apply VarMap.find_1 in Hv_idx.
               apply VarMap.find_1 in Hv_arr_in.
               rewrite Hv_idx in Hm1_idx.
               rewrite Hv_arr_in in Hm1_idx.
               inv Hm1_idx.
               assert (Helper: reflect
                                 (v_idx < val_arr_length v_arr_in)%Z
                                 (v_idx <? val_arr_length v_arr_in)%Z).
               { apply Z.ltb_spec0. }
               apply reflect_iff in Helper.
               apply Helper; auto.
           }
           {
             rewrite Heqinv in *.
             intros v_idx v_arr_in v_arr_out.
             intros Hv_idx Hv_arr_in Hv_arr_out.
             apply VarMap.add_3 in Hv_idx; auto.
             apply VarMap.add_3 in Hv_arr_in; auto.
             apply VarMap.add_3 in Hv_arr_out; auto.
           }
        ** intros m1 m2 Hm1t Hm2t.
           simpl. intros [Hcond2_m1 [Hcond2_m2 Hcond3_m1] ].
           repeat split; try tauto.
        ** fourier.
        ** pose (loopbody2 := (at( arr_out, idx)<- e;; idx <- idx :+ 1%Z)%cmd).
           apply aprhl_equiv
             with (c1 := loopbody2) (c1' := loopbody2)
                  (c2 := i_skip) (c2' := (i_skip ;; i_skip)%cmd);
             try (solve [do 4 inv_welltyped; auto] ).
           unfold loopbody2.
           remember (fun m =>
                       forall v_idx v_arr_out v_e v_arr_out_idx,
                         VarMap.MapsTo idx (v_int v_idx) m
                         -> VarMap.MapsTo arr_out (v_arr t_out' v_arr_out) m
                         -> sem_expr m e = Some v_e
                         -> val_arr_index v_arr_out v_idx = Some v_arr_out_idx
                         -> v_arr_out_idx = v_e
                    ) as cond4.
           remember (fun m =>
                       forall v_idx v_arr_out v_e v_arr_out_idx,
                         VarMap.MapsTo idx (v_int v_idx) m
                         -> VarMap.MapsTo arr_out (v_arr t_out' v_arr_out) m
                         -> sem_expr m e = Some v_e
                         -> val_arr_index v_arr_out (Z.pred v_idx) = Some v_arr_out_idx
                         -> v_arr_out_idx = v_e
                    ) as cond4'.
           replace (0%R) with (0+0)%R by apply Rplus_0_r.
           apply aprhl_seq with (Q := fun m1 m2 =>
                                           cond2 m1
                                         /\ cond2 m2
                                         /\ cond3 m1
                                         /\ cond4 m1
                                         /\ strict_in_bound_cond m1
                                         /\ inv m1);
             try (solve [do 5 inv_welltyped; auto] ).
           eapply aprhl_conseq
             with (Q' :=
                     fun m1 m2 =>
                       cond2 m1 /\ cond2 m2 /\
                       cond3 m1 /\ cond4 m1 /\
                       strict_in_bound_cond m1
                       /\ inv m1); auto;
             try (solve [do 5 inv_welltyped; auto] ).
           apply aprhl_index_assign_L;
             try (solve [do 5 inv_welltyped; auto] ).
           *** intros m1 m2 Hm1t Hm2t.
               intros [Hcond2_m1 [Hcond2_m2 [Hcond3_m1 [Hin_bound_m1 Hinv_m1] ] ] ].
               unfold assign_index_sub_left.
               intros [v_idx Hv_idx].
               intros [t_arr_out [v_arr_out Hv_arr_out] ].
               intros [v_e Hv_e].
               rewrite Hv_idx.
               rewrite Hv_e.
               rewrite Hv_arr_out.
               rewrite Heqstrict_in_bound_cond in Hin_bound_m1.
               simpl in Hv_idx.
               apply VarMap.find_2 in Hv_idx.
               apply VarMap.find_2 in Hv_arr_out.
               rewrite Heqcond2 in Hcond2_m1.
               destruct Hcond2_m1
                 as [v_arr_out' [v_arr_in [Hv_arr_out' [Hv_arr_in Hlength] ] ] ].
               assert (H_v_idx_range: (0 <= v_idx < val_arr_length v_arr_in)%Z).
               {
                 apply Hin_bound_m1; auto.
               }
               rewrite <- Hlength in H_v_idx_range.
               assert (Hv_arr_out_same: v_arr_out = v_arr_out').
               {
                 apply VarMap.find_1 in Hv_arr_out.
                 apply VarMap.find_1 in Hv_arr_out'.
                 rewrite Hv_arr_out in Hv_arr_out'.
                 inv Hv_arr_out'.
                 auto.
               }
               rewrite <- Hv_arr_out_same in *. clear Hv_arr_out_same.
               destruct (val_arr_update_range v_idx v_arr_out v_e)
                 as [v_arr_out2 Hv_arr_out2]; auto.
               rewrite Hv_arr_out2.
               unfold mem_set.
               repeat split; try tauto.
               {
                 rewrite Heqcond2.
                 exists v_arr_out2, v_arr_in.
                 assert (Ht_out_eq: t_arr_out = t_out').
                 {
                   assert (welltyped_val (v_arr t_arr_out v_arr_out) (t_arr t_out')).
                   {
                     apply VarMap.find_2 in Ht_arr_out.
                     apply welltyped_memory_val
                       with (env := stenv) (m := m1) (x := arr_out); auto.
                   }
                   inv H7; auto.
                 }
                 rewrite Ht_out_eq in *.
                 repeat split.
                 - apply VarMap.add_1; auto.
                 - apply VarMap.add_2; auto.
                 - assert (Helper_length: val_arr_length v_arr_out = val_arr_length v_arr_out2).
                   {
                     eapply val_arr_update_length_same; eauto.
                   }
                   rewrite <- Helper_length; auto.
               }
               {
                 rewrite Heqcond3.
                 intros v_idx' v_arr_in' v'.
                 intros Hv_idx' Hv_arr_in' Hv'.
                 rewrite Heqcond3 in Hcond3_m1.
                 apply VarMap.add_3 in Hv_idx'; auto.
                 apply VarMap.add_3 in Hv_arr_in'; auto.
                 apply VarMap.add_2; auto.
                 apply Hcond3_m1 with (v_idx := v_idx') (v_arr_in := v_arr_in'); auto.
               }
               {
                 rewrite Heqcond4.
                 intros v_idx'' v_arr_out'' v_e'' v_arr_out_idx''.
                 intros Hv_idx'' Hv_arr_out'' Hv_e'' Hv_arr_out_idx''.
                 apply VarMap.add_3 in Hv_idx''; auto.
                 collapse_dup_MapsTo. inv Hv_idx_eq_Hv_idx''.
                 assert (Helper_arr_out_eq:
                           VarMap.MapsTo arr_out
                                         (v_arr t_arr_out v_arr_out2)
                                         (VarMap.add arr_out (v_arr t_arr_out v_arr_out2) m1)).
                 {
                   apply VarMap.add_1; auto.
                 }
                 collapse_dup_MapsTo. inv Hv_arr_out''_eq_Helper_arr_out_eq.
                 clear Helper_arr_out_eq.
                 rewrite <- sem_expr_strengthening
                   with (stenv := stenv) (t := t_arr_out) in Hv_e''; auto.
                 rewrite Hv_e'' in Hv_e.
                 inv Hv_e.
                 rewrite val_arr_update_index_same
                   with (vs := v_arr_out) (v := v_e) in Hv_arr_out_idx''; auto.
                 inv Hv_arr_out_idx''. auto.
                 {
                   intros contra.
                   unfold VarSet.Subset in Hsubset.
                   apply Hsubset in contra.
                   apply VarSet.singleton_1 in contra.
                   rewrite contra in H_arr_out_neq_temp.
                   exfalso; auto.
                 }
               }
               {
                 rewrite Heqstrict_in_bound_cond.
                 intros v_idx' v_arr_in'.
                 intros Hv_idx' Hv_arr_in'.
                 apply VarMap.add_3 in Hv_idx'; auto.
                 apply VarMap.add_3 in Hv_arr_in'; auto.
               }
               {
                 rewrite Heqinv.
                 intros v_idx'' v_arr_in'' v_arr_out''.
                 intros Hv_idx'' Hv_arr_in'' Hv_arr_out''.
                 apply VarMap.add_3 in Hv_idx''; auto.
                 apply VarMap.add_3 in Hv_arr_in''; auto.
                 assert (Helper_arr_out_eq:
                           VarMap.MapsTo
                             arr_out
                             (v_arr t_arr_out v_arr_out2)
                             (VarMap.add arr_out (v_arr t_arr_out v_arr_out2) m1)).
                 {
                   apply VarMap.add_1; auto.
                 }
                 collapse_dup_MapsTo. inv Hv_arr_out''_eq_Helper_arr_out_eq.
                 clear Helper_arr_out_eq Hv_arr_out''.
                 collapse_dup_MapsTo. inv Hv_arr_in_eq_Hv_arr_in''. clear Hv_arr_in''.
                 collapse_dup_MapsTo. inv Hv_idx_eq_Hv_idx''. clear Hv_idx''.
                 replace
                   (val_arr_subarr v_arr_out2 v_idx'')
                   with
                     (val_arr_subarr v_arr_out v_idx'').
                 apply Hinv_m1; auto.
                 rewrite <- val_arr_subarr_update with (vs' := v_arr_out2) (v := v_e); auto.
               }
           *** fourier.
           *** eapply aprhl_conseq;
                 try (solve [do 5 inv_welltyped; auto] ).
               apply aprhl_assign_L;
                 try (solve [do 5 inv_welltyped; auto] ).
               {
                 intros m1 m2 Hm1t Hm2t.
                 intros [Hcond2_m1
                           [Hcond2_m2
                              [Hcond3_m1
                                 [Hcond4_m1
                                    [Hstrict_in_bound_cond_m1 Hinv_m1] ] ] ] ].
                 unfold assign_sub_left.
                 intros [v_idx Hv_idx].
                 rewrite Hv_idx.
                 unfold mem_set.
                 instantiate
                   (1 := fun m1 m2 =>
                           cond2 m1
                           /\ cond2 m2
                           /\ in_bound_cond m1
                           /\ inv m1
                   ).
                 repeat split; try tauto.
                 {
                   rewrite Heqcond2.
                   rewrite Heqcond2 in Hcond2_m1.
                   destruct Hcond2_m1
                     as [v_arr_out [v_arr_in [Hv_arr_out [Hv_arr_in Hlength] ] ] ].
                   exists v_arr_out, v_arr_in.
                   repeat split; auto.
                   apply VarMap.add_2; auto.
                   apply VarMap.add_2; auto.
                 }
                 (*
                 {
                   rewrite Heqcond3'.
                   intros v_idx' v_arr_in' v'.
                   intros Hv_idx' Hv_arr_in' Hv'.
                   assert (Helper_v_idx_eq:
                             VarMap.MapsTo idx v_idx (VarMap.add idx v_idx m1)).
                   {
                     apply VarMap.add_1; auto.
                   }
                   collapse_dup_MapsTo. inv Hv_idx'_eq_Helper_v_idx_eq.
                   clear H7.
                   clear Helper_v_idx_eq Hv_idx'.
                   apply VarMap.add_3 in Hv_arr_in'; auto.
                   apply VarMap.add_2; auto.
                   simpl in Hv_idx.
                   destruct (VarMap.find idx m1) as [v_idx1|] eqn:Hv_idx1;
                     try (solve [inv Hv_idx] ).
                   assert (Hv_idx1_int:
                             welltyped_val v_idx1 t_int).
                   {
                     apply welltyped_memory_val
                       with (env := stenv) (m := m1) (x := idx);
                       auto.
                     do 2 inv_welltyped.
                     inv H11. inv H15. auto.
                     apply VarMap.find_2 in Hv_idx1; auto.
                   }
                   inv Hv_idx1_int.
                   inv Hv_idx.
                   replace (z2+1)%Z with (Z.succ z2) in Hv' by omega.
                   rewrite Z.pred_succ in Hv'.
                   apply VarMap.find_2 in Hv_idx1.
                   apply Hcond3_m1
                     with (v_idx := z2) (v_arr_in := v_arr_in'); auto.
                 }
                 {
                   rewrite Heqcond4 in Hcond4_m1.
                   rewrite Heqcond4.
                   intros v_idx' v_arr_out' v_e' v_arr_out_idx'.
                   intros Hv_idx' Hv_arr_out' Hv_e' Hv_arr_out_idx'.
                   rewrite <- sem_expr_strengthening
                     with (stenv := stenv) (t := t_out') in Hv_e'; auto.
                   apply VarMap.add_3 in Hv_arr_out'; auto.
                   assert (VarMap.MapsTo idx v_idx (VarMap.add idx v_idx m1))
                     by (apply VarMap.add_1; auto).
                   collapse_dup_MapsTo. inv Hv_idx'_eq_H7. clear H7 H8 Hv_idx'.
                   simpl in Hv_idx.
                   destruct (VarMap.find idx m1) as [v_idx1|] eqn:Hv_idx1;
                     try (solve [inv Hv_idx] ).
                   apply VarMap.find_2 in Hv_idx1.
                   assert (Hv_idx1_int: welltyped_val v_idx1 t_int).
                   {
                     apply welltyped_memory_val with (env := stenv) (m := m1) (x := idx);
                       auto.
                     do 2 inv_welltyped.
                     inv H11. inv H15. auto.
                   }
                   inv Hv_idx1_int.
                   inv Hv_idx.
                   replace (z2 + 1)%Z with (Z.succ z2) in Hv_arr_out_idx' by omega.
                   rewrite Z.pred_succ in Hv_arr_out_idx'.
                   apply Hcond4_m1 with (v_idx := z2) (v_arr_out := v_arr_out'); auto.
                   {
                     intros contra.
                     apply Hsubset in contra.
                     apply VarSet.singleton_1 in contra.
                     subst; auto.
                   }
                 }
                  *)
                 {
                   rewrite Heqin_bound_cond.
                   rewrite Heqstrict_in_bound_cond in Hstrict_in_bound_cond_m1.
                   intros v_idx' v_arr_in'.
                   intros Hv_idx' Hv_arr_in'.
                   apply VarMap.add_3 in Hv_arr_in'; auto.
                   assert (VarMap.MapsTo idx v_idx (VarMap.add idx v_idx m1))
                     by (apply VarMap.add_1; auto).
                   collapse_dup_MapsTo. inv Hv_idx'_eq_H7. clear H7 H8 Hv_idx'.
                   simpl in Hv_idx.
                   destruct (VarMap.find idx m1) as [v_idx1|] eqn:Hv_idx1;
                     try (solve [inv Hv_idx; auto] ).
                   apply VarMap.find_2 in Hv_idx1.
                   assert (Hv_idx1_int:
                             welltyped_val v_idx1 t_int).
                   {
                     apply welltyped_memory_val
                       with (env := stenv) (m := m1) (x := idx); auto.
                     do 2 inv_welltyped.
                     inv H11.
                     inv H15; auto.
                   }
                   inv Hv_idx1_int. inv Hv_idx.
                   assert (0 <= z2 < val_arr_length v_arr_in')%Z.
                   {
                     apply Hstrict_in_bound_cond_m1; auto.
                   }
                   omega.
                 }
                 {
                   rewrite Heqinv.
                   intros v_idx' v_arr_in' v_arr_out'.
                   intros Hv_idx' Hv_arr_in' Hv_arr_out'.
                   assert (VarMap.MapsTo idx v_idx  (VarMap.add idx v_idx m1))
                     by (apply VarMap.add_1; auto).
                   collapse_dup_MapsTo. inv Hv_idx'_eq_H7. clear H7 H8 Hv_idx'.
                   apply VarMap.add_3 in Hv_arr_out'; auto.
                   apply VarMap.add_3 in Hv_arr_in'; auto.
                   simpl in Hv_idx.
                   destruct (VarMap.find idx m1) as [v_idx1|] eqn:Hv_idx1;
                     try (solve [inv Hv_idx] ).
                   apply VarMap.find_2 in Hv_idx1.
                   assert (Hv_idx1_int: welltyped_val v_idx1 t_int).
                   {
                     apply welltyped_memory_val
                       with (env := stenv) (m := m1) (x := idx); auto.
                     do 2 inv_welltyped.
                     inv H11.
                     inv H15; auto.
                   }
                   inv Hv_idx1_int.
                   inv Hv_idx.
                   remember (z2 + 1)%Z as succ_z2.
                   assert (Hz2_range: (0 <= z2 < val_arr_length v_arr_in')%Z).
                   {
                     apply Hstrict_in_bound_cond_m1; auto.
                   }
                   assert (Hsucc_z2_range:
                             (0 <= succ_z2 <= val_arr_length v_arr_in')%Z).
                   {
                     rewrite Heqsucc_z2. omega.
                   }
                   assert ((x <-- val_arr_subarr v_arr_in' z2 ;;;
                              val_arr_map_option f_e x)%option
                           = val_arr_subarr v_arr_out' z2).
                   {
                     apply Hinv_m1; auto.
                   }
                   assert (exists v_arr_out_idx',
                              val_arr_index v_arr_out' z2 = Some v_arr_out_idx').
                   {
                     apply val_arr_index_range.
                     assert (val_arr_length v_arr_out' = val_arr_length v_arr_in').
                     {
                       destruct Hcond2_m1
                         as [v_arr_out'' [v_arr_in'' [Hv_arr_out'' [Hv_arr_in'' Hlength] ] ] ].
                       collapse_dup_MapsTo.
                       inv Hv_arr_in''_eq_Hv_arr_in'.
                       clear Hv_arr_in''.
                       collapse_dup_MapsTo.
                       inv Hv_arr_out''_eq_Hv_arr_out'.
                       clear Hv_arr_out''.
                       apply Hlength.
                     }
                     rewrite H8.
                     auto.
                   }
                   assert (exists v_arr_in_idx',
                              val_arr_index v_arr_in' z2 = Some v_arr_in_idx').
                   {
                     apply val_arr_index_range; auto.
                   }
                   destruct H8 as [v_arr_out_idx' Hv_arr_out_idx'].
                   destruct H10 as [v_arr_in_idx' Hv_arr_in_idx'].
                   assert (VarMap.MapsTo temp v_arr_in_idx' m1).
                   {
                     apply Hcond3_m1 with (v_idx := z2) (v_arr_in := v_arr_in'); auto.
                   }
                   apply Hf_e in H8.
                   apply lossless_compute_sound
                     with (stenv := stenv) (m := m1) (t := t_out') in Hlossless_e; auto.
                   destruct Hlossless_e as [v_e Hv_e].
                   assert (v_arr_out_idx' = v_e).
                   {
                     apply Hcond4_m1 with (v_idx := z2) (v_arr_out := v_arr_out'); auto.
                   }
                   rewrite Hv_e in H8.
                   rewrite <- H10 in H8.
                   rewrite Heqsucc_z2.
                   replace (z2 + 1)%Z with (Z.succ z2) by omega.
                   apply val_subarr_map_succ with (v1 := v_arr_in_idx') (v2 := v_arr_out_idx'); auto.
                 }
               }
               {
                 intros m1 m2.
                 intros Hm1t Hm2t.
                 simpl.
                 intros [Hcond2_m1
                           [Hcond2_m2
                              [Hin_bound_m1 Hinv'_m1] ] ].
                 repeat split; try tauto.
               }
               {
                 fourier.
               }
      * intros m1 m2 Hm1t Hm2t.
        tauto.
      * intros m1 m2 Hm1t Hm2t.
        intros [Hconds Hidx_m1].
        destruct Hconds as [Hcond2_m1 [Hcond2_m2 [Hin_bound_m1 Hinv_m1] ] ].
        repeat split; try tauto.
      * fourier.
      * (* This is the symmetric case... *) admit.
  - step_envs (z =? 0)%Z Henvs.
Admitted.

Definition is_None (o : option cmd) :=
  match o with
  | None => true
  | _ => false
  end.

(* Filters the type checking results to the list that doesn't have any program
   fragments left *)
Definition get_complete_results (m : M_nondet (env_eps * option cmd)) : M_nondet env_eps :=
  List.map fst (List.filter (fun e_oc => is_None (snd e_oc)) m).

Definition lift_checker
           (m : env
                -> st_env
                -> cmd
                -> M_nondet (env_eps * option cmd))
  : env -> st_env -> cmd -> option (M_nondet env_eps) :=
  fun senv stenv prog =>
  Some (get_complete_results (m senv stenv prog)).

Fixpoint checker
         (fuel: nat)
         (senv: env)
         (stenv: st_env)
         (prog: cmd) :=
  match fuel with
  | O => []
  | S n' =>
    let rule_set := [assign_rule;
                       skip_rule;
                       cond_sens_rule;
                       while_sens_rule;
                       if_nonsens_rule (lift_checker (checker n'));
                       cond_inc_rule;
                       simple_arr_map_rule
                    ]
    in search rule_set prog fuel empty_uni_env senv stenv
  end.

Module Tests.
Definition assn_prog (x : var) :=
  (x <- x :* 2%Z)%cmd.
Definition assn_prog2 :=
  (assn_prog "x";; assn_prog "x";; i_skip)%cmd.
Definition cond_prog :=
  (If 0%Z :< "x"
   then (assn_prog "x" ;; assn_prog "y" ;; assn_prog "y")
   else assn_prog "y"
   end)%cmd.

Definition cond_inc_prog :=
  (If 0%Z :< "x"
   then "x" <- "x" :+ 5%Z
   else "x" <- "x" :+ 10%Z
   end)%cmd.

Definition arr_map_prog :=
  (
    "i" <- 0%Z ;;
    len("out") <- len("in") ;;
    While ("i" :< len("in"))%expr do
      "t" <- ("in" !! "i")%expr ;;
      at("out", "i") <- ("t" :+ "t" :* 2%Z)%expr ;;
      "i" <- ("i" :+ 1%Z)%expr
    end
  )%cmd.

Eval compute in env_max
                  (env_from_list [("x", 2%Z)]%list)
                  (env_from_list [("x", 1%Z); ("y", 10%Z)]%list).

Eval compute in env_max
                  (env_from_list [("x", 1%Z); ("y", 10%Z)]%list)
                  (env_from_list [("x", 2%Z)]%list).

Eval compute in
    search [assign_rule]
           (assn_prog "x")
           1
           empty_uni_env
           (env_from_list [("x", 1%Z)]%list)
           (varmap_from_list [("x", t_int)]%list).
Eval compute in
    search [assign_rule; skip_rule]
           assn_prog2
           100
           empty_uni_env
           (env_from_list [("x", 1%Z)]%list)
           (varmap_from_list [("x", t_int)]%list).
Eval compute in
    search [assign_rule; skip_rule; cond_sens_rule]
           cond_prog
           100
           empty_uni_env
           (env_from_list [("x", 1%Z); ("y", 1%Z)]%list)
           (varmap_from_list [("x", t_int); ("y", t_int)]%list).
Eval compute in
    checker 100
            (env_from_list [("x", 0%Z); ("y", 1%Z)]%list)
            (varmap_from_list [("x", t_int); ("y", t_int)]%list)
            cond_prog.
Eval compute in
    checker 100
            (env_from_list [("x", 1%Z); ("y", 1%Z)]%list)
            (varmap_from_list [("x", t_int); ("y", t_int)]%list)
            cond_prog.
Eval compute in
    checker 100
            (env_from_list [("x", 1%Z)]%list)
            (varmap_from_list [("x", t_int)]%list)
            cond_inc_prog.
Eval compute in
    checker 100
            (env_from_list [("i", 0%Z); ("in", 1%Z); ("out", 0%Z); ("t", 0%Z)]%list)
            (varmap_from_list [("i", t_int); ("in", t_arr t_int); ("out", t_arr t_int); ("t", t_int)]%list)
            arr_map_prog.
End Tests.
End NondetTS.
