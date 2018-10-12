Require Export Coq.Classes.Morphisms.
Require Import Coq.Reals.Reals.

Require Export Cfuzzi.Lib.
Require Export Cfuzzi.BaseDefinitions.
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

  Parameter welltyped_memory_val : forall env m x v (t : tau),
      welltyped_memory env m
      -> VarMap.MapsTo x t env
      -> VarMap.MapsTo x v m
      -> welltyped_val v t.

  Parameter sem_expr : memory -> expr -> option val.

  Parameter sem_expr_val_typed : forall env m e v t,
    welltyped_expr env e t
    -> sem_expr m e = Some v
    -> welltyped_memory env m
    -> welltyped_val v t.

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

Hint Unfold welltyped_memory.

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

Lemma welltyped_memory_val : forall env m x v (t : tau),
    welltyped_memory env m
    -> VarMap.MapsTo x t env
    -> VarMap.MapsTo x v m
    -> welltyped_val v t.
Proof.
  intros env m x v t.
  intros Hmem Hxt Hxvm.
  unfold welltyped_memory in Hmem.
  destruct (Hmem x t) as [v2 [Hxv2 Hv2t]]; auto.
  apply VarMap.find_1 in Hxvm; apply VarMap.find_1 in Hxv2.
  rewrite Hxv2 in Hxvm; inv Hxvm; auto.
Qed.

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
    inv Hv.
    constructor.
  - intros m v Hv Hmem.
    simpl in Hv.
    apply VarMap.find_2 in Hv.
    apply welltyped_memory_val with (env := env) (m := m) (x := x); auto.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H3.
      constructor; auto.
      constructor; auto.
    + destruct v0; inv H3.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      inv Hv.
    + destruct v0; destruct v1; inv H2.
      constructor; auto.
    + destruct v0; inv H2.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      try (solve [inversion Hv|destruct v0; inversion Hv]).
    destruct v0 eqn:Hv0;
      destruct v1 eqn:Hv1;
      try (solve [inversion Hv]); subst.
    + apply val_arr_index_welltyped with (vs := v2) (idx := z) (t1 := t0); auto.
      apply IHwelltyped_expr1 with (m := m); auto.
    + assert (welltyped_val (v_bag t0 v2) (t_arr t)). {
        apply IHwelltyped_expr1 with (m := m); auto.
      }
      inversion H1.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e1) eqn:He1;
      destruct (sem_expr m e2) eqn:He2;
      try (solve [inversion Hv|destruct v0; inversion Hv]).
    destruct v0 eqn:Hv0;
      destruct v1 eqn:Hv1;
      try (solve [inversion Hv]); subst.
    + assert (welltyped_val (v_arr t0 v2) (t_bag t)). {
        apply IHwelltyped_expr1 with (m := m); auto.
      }
      inv H1.
    + apply val_bag_index_welltyped with (vs := v2) (idx := z) (t1 := t0); auto.
      apply IHwelltyped_expr1 with (m := m); auto.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e) as [ev|] eqn:He; try (solve [inversion Hv]).
    destruct ev eqn:Hev; try (solve [inversion Hv]); inv Hv; subst.
    + constructor.
    + constructor.
  - intros m v Hv Hmem.
    simpl in Hv.
    destruct (sem_expr m e) as [ev|] eqn:He; try (solve [inversion Hv]).
    destruct ev eqn:Hev; try (solve [inversion Hv]); inv Hv; subst.
    + constructor.
    + constructor.
Qed.

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
  | bi_index_assign x eidx erhs =>
    match VarMap.find x m,
          sem_expr m eidx,
          sem_expr m erhs with
    | Some (v_arr t vs), Some (v_int idx), Some v
      => match val_arr_update vs idx v with
        | Some vs' => Munit (VarMap.add x (v_arr t vs') m)
        | None => distr0
         end
    | Some (v_bag t vs), Some (v_int idx), Some v
      => match val_arr_update vs idx v with
        | Some vs' => Munit (VarMap.add x (v_bag t vs') m)
        | None => distr0
        end
    | _, _, _
      => distr0
    end
  | bi_length_assign x rhs =>
    match VarMap.find x m,
          sem_expr m rhs with
    | Some (v_arr t vs), Some (v_int len)
      => match val_arr_update_length t vs len with
         | Some vs' => Munit (VarMap.add x (v_arr t vs') m)
         | None => distr0
         end
    | Some (v_bag t vs), Some (v_int len)
      => match val_arr_update_length t vs len with
         | Some vs' => Munit (VarMap.add x (v_bag t vs') m)
         | None => distr0
         end
    | _, _ => distr0
    end
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
Ltac ty_val v :=
  match goal with
  | [
    H1 : welltyped_expr ?env ?expr ?t,
    H2 : sem_expr ?m ?expr = Some v
    |- _ ] =>
    let H := fresh "H_type_" v in
    assert (H : welltyped_val v t) by
    (apply sem_expr_val_typed
       with (env := env) (m := m) (e := expr);
     auto)
  | [
    H1: VarMap.MapsTo ?x v ?m,
    H2: welltyped_memory ?env ?m,
    H3: VarMap.MapsTo ?x ?t ?env
    |- _ ] =>
    let H := fresh "H_type_" v in
    assert (H : welltyped_val v t) by
        apply (welltyped_memory_val env m x v t H2 H3 H1)
  end.
Ltac simpl_distr_monad := repeat (simpl; unfold star, unit).

Lemma welltyped_distr0: forall env,
    range (fun cm => welltyped env (fst cm)
                     /\ welltyped_memory env (snd cm)) distr0.
Proof.
  intros env; unfold range.
  intros f Hf.
  simpl_distr_monad.
  unfold Mdistr0.
  reflexivity.
Qed.

Hint Resolve welltyped_distr0.

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
    destruct (sem_expr m rhs) as [v_rhs|] eqn:H_v_rhs; auto.
    simpl_distr_monad.
    rewrite <- Hf; auto.
    split; auto.
    simpl.
    ty_val v_rhs.
    apply welltyped_memory_add with (t := t); auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct (sem_expr m center) as [v_center|] eqn:H_v_center; auto.
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
    simpl_distr_monad.
    destruct (VarMap.find x m) as [v_x|] eqn:H_x_v; auto.
    apply VarMap.find_2 in H_x_v.
    ty_val v_x.
    inv H_type_v_x;
      destruct (sem_expr m eidx) as [v_idx|] eqn:H_v_idx; auto;
        ty_val v_idx;
        inv H_type_v_idx;
        destruct (sem_expr m erhs) as [v_rhs|] eqn:H_v_rhs; auto;
          ty_val v_rhs.
    + simpl; destruct z; auto.
    + destruct (val_arr_update (v_cons v vs) z v_rhs) eqn:H_vs'; auto.
      simpl_distr_monad.
      rewrite <- Hf; auto.
      split; simpl; auto.
      apply welltyped_memory_add with (t := t_arr t); auto.
      apply val_arr_update_welltyped with (vs := (v_cons v vs)) (idx := z) (v := v_rhs); auto.
      constructor; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct (VarMap.find x m) as [v_x|] eqn:H_x_v; auto.
    apply VarMap.find_2 in H_x_v.
    ty_val v_x.
    inv H_type_v_x;
      destruct (sem_expr m eidx) as [v_idx|] eqn:H_v_idx; auto;
        ty_val v_idx;
        inv H_type_v_idx;
        destruct (sem_expr m erhs) as [v_rhs|] eqn:H_v_rhs; auto;
          ty_val v_rhs.
    + simpl; destruct z; auto.
    + destruct (val_arr_update (v_cons v vs) z v_rhs) eqn:H_vs'; auto.
      simpl_distr_monad.
      rewrite <- Hf; auto.
      split; simpl; auto.
      apply welltyped_memory_add with (t := t_bag t); auto.
      apply val_bag_update_welltyped with (vs := (v_cons v vs)) (idx := z) (v := v_rhs); auto.
      constructor; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct (VarMap.find x m) as [v_x|] eqn:H_v_x; auto.
    apply VarMap.find_2 in H_v_x.
    ty_val v_x.
    inv H_type_v_x; auto;
      destruct (sem_expr m erhs) as [v_rhs|] eqn:H_v_rhs; auto;
        ty_val v_rhs;
        inv H_type_v_rhs.
    + destruct (val_arr_update_length t v_nil z) eqn:Harr; auto.
      simpl_distr_monad.
      rewrite <- Hf; auto.
      split; simpl; auto.
      apply welltyped_memory_add with (t := (t_arr t)); auto.
      apply val_arr_update_length_welltyped with (vs := v_nil) (n := z); auto.
      constructor.
    + destruct (val_arr_update_length t (v_cons v vs) z) eqn:Harr; auto.
      simpl_distr_monad.
      rewrite <- Hf; auto.
      split; simpl; auto.
      apply welltyped_memory_add with (t := (t_arr t)); auto.
      apply val_arr_update_length_welltyped with (vs := (v_cons v vs)) (n := z); auto.
      constructor; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct (VarMap.find x m) as [v_x|] eqn:H_v_x; auto.
    apply VarMap.find_2 in H_v_x.
    ty_val v_x.
    inv H_type_v_x; auto;
      destruct (sem_expr m erhs) as [v_rhs|] eqn:H_v_rhs; auto;
        ty_val v_rhs;
        inv H_type_v_rhs.
    + destruct (val_arr_update_length t v_nil z) eqn:Harr; auto.
      simpl_distr_monad.
      rewrite <- Hf; auto.
      split; simpl; auto.
      apply welltyped_memory_add with (t := (t_bag t)); auto.
      apply val_bag_update_length_welltyped with (vs := v_nil) (n := z); auto.
      constructor.
    + destruct (val_arr_update_length t (v_cons v vs) z) eqn:Harr; auto.
      simpl_distr_monad.
      rewrite <- Hf; auto.
      split; simpl; auto.
      apply welltyped_memory_add with (t := (t_bag t)); auto.
      apply val_bag_update_length_welltyped with (vs := (v_cons v vs)) (n := z); auto.
      constructor; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct (sem_expr m e) as [v_e|] eqn:H_v_e; auto.
    ty_val v_e.
    inversion H_type_v_e; subst; clear H_type_v_e.
    destruct b;
      simpl_distr_monad;
      rewrite <- Hf; auto.
  - intros m Hmem f Hf.
    simpl_distr_monad.
    destruct (sem_expr m e) as [v_e|] eqn:H_v_e; auto.
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
Qed.

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
