Require Export Cfuzzi.Syntax.
Require Export Cfuzzi.VariableDefinitions.
Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.

Definition st_env := VarMap.t tau.

Inductive welltyped_val : val -> tau -> Prop :=
| welltyped_int : forall z, welltyped_val (v_int z) t_int
| welltyped_bool : forall b, welltyped_val (v_bool b) t_bool
| welltyped_arr_nil : forall t, welltyped_val (v_arr t v_nil) (t_arr t)
| welltyped_arr_cons : forall v vs t, welltyped_val v t
                                 -> welltyped_val (v_arr t vs) (t_arr t)
                                 -> welltyped_val (v_arr t (v_cons v vs)) (t_arr t)
| welltyped_bag_nil : forall t, welltyped_val (v_bag t v_nil) (t_bag t)
| welltyped_bag_cons : forall v vs t, welltyped_val v t
                                 -> welltyped_val (v_bag t vs) (t_bag t)
                                 -> welltyped_val (v_bag t (v_cons v vs)) (t_bag t).

Lemma tau_default_welltyped :
  forall t, welltyped_val (tau_default_val t) t.
Proof.
  destruct t; constructor.
Qed.

Hint Resolve tau_default_welltyped.

Lemma val_arr_index_nat_welltyped :
  forall t vs idx v,
    welltyped_val (v_arr t vs) (t_arr t)
    -> val_arr_index_nat vs idx = Some v
    -> welltyped_val v t.
Proof.
  intros t vs idx v Htyped.
  remember (v_arr t vs) as varr.
  remember (t_arr t) as tarr.
  generalize dependent idx.
  generalize dependent t.
  generalize dependent v.
  generalize dependent vs.
  induction Htyped; try (solve [intros vs v t Harr contra; inversion contra]).
  - intros vs v t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
    unfold val_arr_index in Hv.
    simpl in Hv; inversion Hv.
  - intros vs' v' t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
    destruct idx as [|idx].
    + simpl in Hv; inversion Hv; subst; auto.
    + simpl in Hv; inversion Hv; subst; auto.
      apply IHHtyped2 with (vs0 := vs) (idx := idx); auto.
  - intros vs v t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
  - intros vs' v' t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
Qed.

Lemma val_arr_index_welltyped :
  forall t vs idx v,
    welltyped_val (v_arr t vs) (t_arr t)
    -> val_arr_index vs idx = Some v
    -> welltyped_val v t.
Proof.
  intros t vs idx v Htyped Hv.
  destruct idx eqn:Hidx.
  - simpl in Hv; inversion Hv; subst; clear Hv.
    eapply val_arr_index_nat_welltyped; eauto.
  - simpl in Hv; inversion Hv; subst; clear Hv.
    eapply val_arr_index_nat_welltyped; eauto.
  - simpl in Hv; inversion Hv.
Qed.

Lemma val_bag_index_nat_welltyped :
  forall t vs idx v,
    welltyped_val (v_bag t vs) (t_bag t)
    -> val_arr_index_nat vs idx = Some v
    -> welltyped_val v t.
Proof.
  intros t vs idx v Htyped.
  remember (v_bag t vs) as varr.
  remember (t_bag t) as tarr.
  generalize dependent idx.
  generalize dependent t.
  generalize dependent v.
  generalize dependent vs.
  induction Htyped; try (solve [intros vs v t Harr contra; inversion contra]).
  - intros vs v t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
  - intros vs' v' t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
  - intros vs v t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
    unfold val_arr_index in Hv.
    simpl in Hv; inversion Hv.
  - intros vs' v' t' Hvarr Htarr idx Hv.
    inversion Hvarr; inversion Htarr; subst; clear Hvarr; clear Htarr.
    destruct idx as [|idx].
    + simpl in Hv; inversion Hv; subst; auto.
    + simpl in Hv; inversion Hv; subst; auto.
      apply IHHtyped2 with (vs0 := vs) (idx := idx); auto.
Qed.

Lemma val_bag_index_welltyped :
  forall t vs idx v,
    welltyped_val (v_bag t vs) (t_bag t)
    -> val_arr_index vs idx = Some v
    -> welltyped_val v t.
Proof.
  intros t vs idx v Htyped Hv.
  destruct idx eqn:Hidx.
  - simpl in Hv; inversion Hv; subst; clear Hv.
    eapply val_bag_index_nat_welltyped; eauto.
  - simpl in Hv; inversion Hv; subst; clear Hv.
    eapply val_bag_index_nat_welltyped; eauto.
  - simpl in Hv; inversion Hv.
Qed.

Inductive welltyped_expr : st_env -> expr -> tau -> Prop :=
| welltyped_lit : forall env z, welltyped_expr env (e_lit z) t_int
| welltyped_var : forall env x t, VarMap.MapsTo x t env -> welltyped_expr env (e_var x) t
| welltyped_add : forall env e1 e2, welltyped_expr env e1 t_int
                               -> welltyped_expr env e2 t_int
                               -> welltyped_expr env (e_add e1 e2) t_int
| welltyped_minus : forall env e1 e2, welltyped_expr env e1 t_int
                                 -> welltyped_expr env e2 t_int
                                 -> welltyped_expr env (e_minus e1 e2) t_int
| welltyped_mult : forall env e1 e2, welltyped_expr env e1 t_int
                                -> welltyped_expr env e2 t_int
                                -> welltyped_expr env (e_mult e1 e2) t_int
| welltyped_div : forall env e1 e2, welltyped_expr env e1 t_int
                               -> welltyped_expr env e2 t_int
                               -> welltyped_expr env (e_div e1 e2) t_int
| welltyped_lt : forall env e1 e2, welltyped_expr env e1 t_int
                              -> welltyped_expr env e2 t_int
                              -> welltyped_expr env (e_lt e1 e2) t_bool
| welltyped_eq : forall env e1 e2 t, welltyped_expr env e1 t
                                -> welltyped_expr env e2 t
                                -> t = t_int \/ t = t_bool
                                -> welltyped_expr env (e_eq e1 e2) t_bool
| welltyped_and : forall env e1 e2, welltyped_expr env e1 t_bool
                               -> welltyped_expr env e2 t_bool
                               -> welltyped_expr env (e_and e1 e2) t_bool
| welltyped_or : forall env e1 e2, welltyped_expr env e1 t_bool
                              -> welltyped_expr env e2 t_bool
                              -> welltyped_expr env (e_or e1 e2) t_bool
| welltyped_arr_index : forall env e1 e2 t, welltyped_expr env e1 (t_arr t)
                                            -> welltyped_expr env e2 t_int
                                            -> welltyped_expr env (e_index e1 e2) t
| welltyped_bag_index : forall env e1 e2 t, welltyped_expr env e1 (t_bag t)
                                            -> welltyped_expr env e2 t_int
                                            -> welltyped_expr env (e_index e1 e2) t
| welltyped_arr_length : forall env e t, welltyped_expr env e (t_arr t)
                                         -> welltyped_expr env (e_length e) t_int
| welltyped_bag_length : forall env e t, welltyped_expr env e (t_bag t)
                                         -> welltyped_expr env (e_length e) t_int
.

Hint Constructors welltyped_expr.

Inductive welltyped : st_env -> cmd -> Prop :=
| welltyped_skip : forall env, welltyped env i_skip
| welltyped_assign : forall env x rhs t,
    VarMap.MapsTo x t env
    -> welltyped_expr env rhs t
    -> welltyped env (i_base_instr (bi_assign x rhs))
| welltyped_laplace : forall env x w center,
    VarMap.MapsTo x t_int env
    -> welltyped_expr env center t_int
    -> welltyped env (i_base_instr (bi_laplace x w center))
| welltyped_arr_index_assign : forall env x eidx erhs t,
    VarMap.MapsTo x (t_arr t) env
    -> welltyped_expr env eidx t_int
    -> welltyped_expr env erhs t
    -> welltyped env (i_base_instr (bi_index_assign x eidx erhs))
| welltyped_bag_index_assign : forall env x eidx erhs t,
    VarMap.MapsTo x (t_bag t) env
    -> welltyped_expr env eidx t_int
    -> welltyped_expr env erhs t
    -> welltyped env (i_base_instr (bi_index_assign x eidx erhs))
| welltyped_arr_length_assign : forall env x erhs t,
    VarMap.MapsTo x (t_arr t) env
    -> welltyped_expr env erhs t_int
    -> welltyped env (i_base_instr (bi_length_assign x erhs))
| welltyped_bag_length_assign : forall env x erhs t,
    VarMap.MapsTo x (t_bag t) env
    -> welltyped_expr env erhs t_int
    -> welltyped env (i_base_instr (bi_length_assign x erhs))
| welltyped_cond : forall env e c1 c2,
    welltyped_expr env e t_bool
    -> welltyped env c1
    -> welltyped env c2
    -> welltyped env (i_cond e c1 c2)
| welltyped_while : forall env e c,
    welltyped_expr env e t_bool
    -> welltyped env c
    -> welltyped env (i_while e c)
| welltyped_seq : forall env c1 c2,
    welltyped env c1
    -> welltyped env c2
    -> welltyped env (i_seq c1 c2).

Hint Constructors welltyped.

Fixpoint welltyped_expr_compute
         (env : st_env) (e : expr) : option tau :=
  match e with
  | e_lit _ => Some t_int
  | e_var x => VarMap.find x env
  | e_add e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_int, Some t_int => Some t_int
    | _, _ => None
    end
  | e_minus e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_int, Some t_int => Some t_int
    | _, _ => None
    end
  | e_mult e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_int, Some t_int => Some t_int
    | _, _ => None
    end
  | e_div e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_int, Some t_int => Some t_int
    | _, _ => None
    end
  | e_lt e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_int, Some t_int => Some t_bool
    | _, _ => None
    end
  | e_eq e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_int, Some t_int => Some t_bool
    | Some t_bool, Some t_bool => Some t_bool
    | _, _ => None
    end
  | e_and e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_bool, Some t_bool => Some t_bool
    | _, _ => None
    end
  | e_or e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some t_bool, Some t_bool => Some t_bool
    | _, _ => None
    end
  | e_index e1 e2 =>
    match welltyped_expr_compute env e1,
          welltyped_expr_compute env e2
    with
    | Some (t_arr t), Some t_int => Some t
    | Some (t_bag t), Some t_int => Some t
    | _, _ => None
    end
  | e_length e =>
    match welltyped_expr_compute env e with
    | Some (t_arr t) => Some t_int
    | Some (t_bag t) => Some t_int
    | _ => None
    end
  end.

Definition welltyped_base_instr_compute (env : st_env) (bi : base_instr) : bool :=
  match bi with
  | bi_assign x e => match VarMap.find x env, welltyped_expr_compute env e with
                    | Some tx, Some te => if tau_eqdec tx te then true else false
                    | _, _ => false
                    end
  | bi_laplace x w e => match VarMap.find x env, welltyped_expr_compute env e with
                       | Some t_int, Some t_int => true
                       | _, _ => false
                        end
  | bi_index_assign x eidx erhs => match VarMap.find x env,
                                         welltyped_expr_compute env eidx,
                                         welltyped_expr_compute env erhs
                                   with
                                   | Some (t_arr t), Some t_int, Some t'
                                     => if tau_eqdec t t'
                                        then true
                                        else false
                                   | Some (t_bag t), Some t_int, Some t'
                                     => if tau_eqdec t t'
                                        then true
                                        else false
                                   | _, _, _ => false
                                   end
  | bi_length_assign x erhs => match VarMap.find x env,
                                     welltyped_expr_compute env erhs
                               with
                               | Some (t_arr t), Some t_int
                                 => true
                               | Some (t_bag t), Some t_int
                                 => true
                               | _, _ => false
                               end
  end.

Fixpoint welltyped_cmd_compute (env : st_env) (c : cmd) {struct c} : bool :=
  match c with
  | i_skip => true
  | i_base_instr bi => welltyped_base_instr_compute env bi
  | i_cond e c1 c2 => match welltyped_expr_compute env e with
                     | Some t_bool => welltyped_cmd_compute env c1 && welltyped_cmd_compute env c2
                     | _ => false
                     end
  | i_while e c => match welltyped_expr_compute env e with
                  | Some t_bool => welltyped_cmd_compute env c
                  | _ => false
                  end
  | i_seq c1 c2 => welltyped_cmd_compute env c1 && welltyped_cmd_compute env c2
  end.

Lemma welltyped_expr_if_computed : forall env e t,
    welltyped_expr_compute env e = Some t -> welltyped_expr env e t.
Proof.
  induction e.
  - simpl; intros t H; inversion H; auto.
  - simpl; intros t H; apply VarMap.find_2 in H; auto.
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht;
        [destruct t0; destruct t1; inversion Ht'; subst; clear Ht';
         [constructor; auto]
        | destruct t0; inversion Ht'].
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht;
        [destruct t0; destruct t1; inversion Ht'; subst; clear Ht';
         [constructor; auto]
        | destruct t0; inversion Ht'].
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht;
        [destruct t0; destruct t1; inversion Ht'; subst; clear Ht';
         [constructor; auto]
        | destruct t0; inversion Ht'].
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht;
        [destruct t0; destruct t1; inversion Ht'; subst; clear Ht';
         [constructor; auto]
        | destruct t0; inversion Ht'].
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht;
        [destruct t0; destruct t1; inversion Ht'; subst; clear Ht';
         [constructor; auto]
        | destruct t0; inversion Ht'].
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht.
    + destruct t0; destruct t1; inversion Ht'; subst; clear Ht'.
      eapply welltyped_eq; eauto.
      eapply welltyped_eq; eauto.
    + destruct t0; inversion Ht'; subst.
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht.
    + destruct t0; destruct t1; inversion Ht'; subst; clear Ht'.
      constructor; auto.
    + destruct t0; inversion Ht'; subst.
  - intros t Ht;
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; try rewrite He2 in Ht);
      inversion Ht as [Ht']; subst; clear Ht.
    + destruct t0; destruct t1; inversion Ht'; subst; clear Ht'.
      constructor; auto.
    + destruct t0; inversion Ht'; subst.
  - intros t Ht.
    destruct (welltyped_expr_compute env e1) eqn:He1;
      destruct (welltyped_expr_compute env e2) eqn:He2;
      simpl in Ht;
      try (rewrite He1 in Ht; rewrite He2 in Ht; inversion Ht as [Ht']; subst; clear Ht).
    + destruct t0;
        destruct t1; try inversion Ht'; subst; clear Ht'.
      apply welltyped_arr_index; auto.
      apply welltyped_bag_index; auto.
    + destruct t0; try inversion Ht'; subst; clear Ht'.
    + rewrite He1 in Ht; inversion Ht.
    + rewrite He1 in Ht; inversion Ht.
  - intros t Ht.
    simpl in Ht.
    destruct (welltyped_expr_compute env e) eqn:He.
    destruct t0; try inversion Ht; subst; clear Ht.
    apply welltyped_arr_length with (t := t0); auto.
    apply welltyped_bag_length with (t := t0); auto.
    inversion Ht.
Qed.

Lemma welltyped_expr_computed_if_prop : forall env e t,
    welltyped_expr env e t -> welltyped_expr_compute env e = Some t.
Proof.
  intros env e t H.
  induction H.
  - auto.
  - simpl; apply VarMap.find_1; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - destruct H1; subst; simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr1; rewrite IHwelltyped_expr2; auto.
  - simpl; rewrite IHwelltyped_expr; auto.
  - simpl; rewrite IHwelltyped_expr; auto.
Qed.

Lemma welltyped_expr_iff : forall env e t,
    welltyped_expr env e t <-> welltyped_expr_compute env e = Some t.
Proof.
  split;
  [ apply welltyped_expr_computed_if_prop |
    apply welltyped_expr_if_computed
  ].
Qed.

Lemma welltyped_if_computed : forall env c,
    welltyped_cmd_compute env c = true -> welltyped env c.
Proof.
  intros env c.
  induction c.
  - simpl; auto.
  - destruct b eqn:Hbi.
    + intros H.
      inversion H; subst; clear H.
      destruct (VarMap.find v env) eqn:Htau_v.
      destruct (welltyped_expr_compute env e) eqn:Htau_e.
      destruct (tau_eqdec t t0).
      * subst; apply VarMap.find_2 in Htau_v.
        apply welltyped_expr_iff in Htau_e.
        apply welltyped_assign with (t := t0); auto.
      * inversion H1.
      * inversion H1.
      * inversion H1.
    + intros H.
      inversion H; subst; clear H.
      destruct (VarMap.find v env) eqn:Htau_v.
      destruct (welltyped_expr_compute env e) eqn:Htau_e.
      destruct t; destruct t0; try inversion H1; clear H1;
        apply VarMap.find_2 in Htau_v; apply welltyped_expr_iff in Htau_e.
      * constructor; auto.
      * destruct t; inversion H1.
      * inversion H1.
    + intros H.
      inversion H; subst; clear H.
      destruct (VarMap.find v env) eqn:Hv; try inversion Hv; subst; clear Hv.
      destruct t; try inversion H1; subst; clear H1.
      destruct (welltyped_expr_compute env e) eqn:He;
        destruct (welltyped_expr_compute env e0) eqn:He0;
        inversion H2; subst; clear H2.
      destruct t0; try inversion H1; subst; clear H1.
      destruct (tau_eqdec t t1); try inversion H2; subst; auto.
      apply welltyped_arr_index_assign with (t := t1); auto.
      apply VarMap.find_2 in H0; auto.
      apply welltyped_expr_iff in He; auto.
      apply welltyped_expr_iff in He0; auto.
      destruct t0; inversion H1.
      destruct (welltyped_expr_compute env e) as [et|] eqn:He.
      destruct et; inversion H2; subst; clear H2.
      destruct (welltyped_expr_compute env e0) as [et0|] eqn:He0.
      destruct (tau_eqdec t et0).
      apply welltyped_bag_index_assign with (t := t); auto.
      apply VarMap.find_2 in H0; auto.
      apply welltyped_expr_iff; auto.
      apply welltyped_expr_iff; auto.
      subst; auto.
      inversion H1.
      inversion H1.
      inversion H2.
      inversion H1.
    + simpl; intros H.
      destruct (VarMap.find v env) eqn:Hv; try inversion H; subst; clear H.
      destruct t; try inversion H1; subst; clear H1.
      * destruct (welltyped_expr_compute env e) eqn:Het; try inversion H0; subst; clear H0.
        destruct t0; try inversion H1; subst; clear H1.
        apply welltyped_arr_length_assign with (t := t); auto.
        apply VarMap.find_2; auto.
        apply welltyped_expr_iff; auto.
      * destruct (welltyped_expr_compute env e) eqn:Het; try inversion H0; subst; clear H0.
        destruct t0; try inversion H1; subst; clear H1.
        apply welltyped_bag_length_assign with (t := t); auto.
        apply VarMap.find_2; auto.
        apply welltyped_expr_iff; auto.
  - intros H.
    inversion H; clear H.
    destruct (welltyped_expr_compute env e) eqn:Htau_e.
    destruct t; try inversion H1.
    + apply andb_true_iff in H1; clear H0.
      destruct H1 as [Hc1 Hc2].
      constructor; auto.
      apply welltyped_expr_iff in Htau_e; auto.
    + inversion H1.
  - intros H.
    inversion H; clear H.
    destruct (welltyped_expr_compute env e) eqn:Htau_e.
    destruct t; try inversion H1.
    + apply welltyped_expr_iff in Htau_e.
      constructor; auto.
    + inversion H1.
  - intros H.
    inversion H; clear H.
    apply andb_true_iff in H1.
    destruct H1 as [Hc1 Hc2].
    constructor; auto.
Qed.

Lemma welltyped_computed_if_prop : forall env c,
    welltyped env c -> welltyped_cmd_compute env c = true.
Proof.
  intros env c H.
  induction H; auto.
  - simpl.
    apply welltyped_expr_iff in H0; rewrite H0.
    apply VarMap.find_1 in H; rewrite H.
    destruct (tau_eqdec t t); auto.
  - simpl.
    apply welltyped_expr_iff in H0; rewrite H0.
    apply VarMap.find_1 in H; rewrite H.
    reflexivity.
  - simpl.
    apply welltyped_expr_iff in H0; rewrite H0.
    apply welltyped_expr_iff in H1; rewrite H1.
    apply VarMap.find_1 in H; rewrite H.
    destruct (tau_eqdec t t); try reflexivity.
    exfalso; apply n; auto.
  - simpl.
    apply welltyped_expr_iff in H0; rewrite H0.
    apply welltyped_expr_iff in H1; rewrite H1.
    apply VarMap.find_1 in H; rewrite H.
    destruct (tau_eqdec t t); try reflexivity.
    exfalso; apply n; auto.
  - simpl.
    apply VarMap.find_1 in H; rewrite H.
    apply welltyped_expr_iff in H0; rewrite H0.
    auto.
  - simpl.
    apply VarMap.find_1 in H; rewrite H.
    apply welltyped_expr_iff in H0; rewrite H0.
    auto.
  - simpl.
    apply welltyped_expr_iff in H.
    rewrite IHwelltyped1; rewrite IHwelltyped2.
    rewrite H.
    auto.
  - simpl.
    apply welltyped_expr_iff in H.
    rewrite H; auto.
  - simpl.
    rewrite IHwelltyped1; rewrite IHwelltyped2; auto.
Qed.

Lemma welltyped_iff : forall env c,
    welltyped env c <-> welltyped_cmd_compute env c = true.
Proof.
  split;
  [ apply welltyped_computed_if_prop |
    apply welltyped_if_computed ].
Qed.

Lemma welltyped_expr_uniq : forall env e t1 t2,
    welltyped_expr env e t1
    -> welltyped_expr env e t2
    -> t1 = t2.
Proof.
  intros env e t1 t2.
  rewrite welltyped_expr_iff.
  rewrite welltyped_expr_iff.
  intros Ht1 Ht2.
  rewrite Ht1 in Ht2.
  inversion Ht2; auto.
Qed.

Lemma welltyped_expr_dec : forall env e t,
    {welltyped_expr env e t} + {~(welltyped_expr env e t)}.
Proof.
  intros env e t.
  destruct (welltyped_expr_compute env e) eqn:He.
  destruct (tau_eqdec t t0); subst.
  - apply welltyped_expr_iff in He; left; auto.
  - right; intros contra.
    apply welltyped_expr_iff in He.
    assert (t = t0). {
      eapply welltyped_expr_uniq; eauto.
    }
    apply n; auto.
  - right; intros contra.
    apply welltyped_expr_iff in contra.
    rewrite contra in He.
    inversion He.
Qed.

Lemma welltyped_cmd_dec : forall env c,
    {welltyped env c} + {~(welltyped env c)}.
Proof.
  intros env c.
  destruct (welltyped_cmd_compute env c) eqn:Htyped.
  - apply welltyped_iff in Htyped; left; auto.
  - right; intros contra.
    apply welltyped_iff in contra. rewrite Htyped in contra; inversion contra.
Defined.
