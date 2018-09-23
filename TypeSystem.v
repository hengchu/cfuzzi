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

  Definition L1_metric : forall A, Metric A -> Metric (list A).
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

  Definition bag_metric : forall A, (forall (x y: A), {x = y} + {x <> y}) -> Metric (list A).
  Proof.
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
  Qed.

End Metrics.

Fixpoint L1_relation (t : tau) (v1 v2 : list (tau_denote t)) (z : Z) : Prop :=
  match v1, v2 with
  | List.nil, List.nil => (z >= 0)%Z
  | v1 :: vs1, v2 :: vs2 =>
    L1_relation t vs1 vs2 (z - Zabs (v1 - v2)%Z)
  | _, _ => False
  end.

Definition dist_relation (t : tau) (v1 v2 : tau_denote t) (z : Z) : Prop :=
  match t as t' return (tau_denote t' -> tau_denote t'-> Prop) with
  | t_int => fun v1 v2 => (Zabs (v1 - v2)%Z <= z)%Z
  | t_bool => fun v1 v2 => if (z =? 0)%Z then (v1 = v2) else True
  end v1 v2.

Inductive env {ts : list tau} : Type :=
| env_nil : env
| env_cons : forall {t}, var t ts -> Z -> env -> env.

Program Fixpoint env_update {t ts} (e : env) (x : var t ts) (d : Z) : env :=
  match e with
  | env_nil => env_cons x d env_nil
  | env_cons _ x' d' e' =>
    if member_eq tau_eqdec x' x
    then env_cons x d e'
    else env_cons x' d' (env_update e' x d)
  end.

Program Fixpoint env_remove {t ts} (e : env) (x : var t ts) : env :=
  match e with
  | env_nil => env_nil
  | env_cons _ x' d' e' =>
    if member_eq tau_eqdec x' x
    then env_remove e' x
    else env_cons x' d' (env_remove e' x)
  end.

Program Fixpoint denote_env {ts} (e : env) : memory_relation ts :=
  match e with
  | env_nil =>
    fun m1 m2 => True
  | env_cons _t x d tl =>
    fun m1 m2 => (dist_relation _t (h_get m1 x) (h_get m2 x) d)
                 /\ (denote_env _ m1 m2)
  end.

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

(* A typechecker for the base language *)
Definition typechecker {ts} := @env ts -> cmd ts -> (R * @env ts)%type.
(* The theorem we need to prove to establish the validity of a typing rule in apRHL *)
Definition typechecker_valid {ts} (tc : @typechecker ts) :=
  forall e_pre c,
    let eps := fst (tc e_pre c) in
    let e_post := snd (tc e_pre c) in
    (c ~_(eps) c : denote_env e_pre ==> denote_env e_post)%triple.

(* A type system for the base language *)
Definition typesystem {ts} := @env ts -> cmd ts -> R -> @env ts -> Prop.
(* The theorem we need to prove to show a typesystem is sound *)
Definition typesystem_valid {ts} (T : @typesystem ts) :=
  forall pre post c eps,
    (T pre c eps post -> c ~_(eps) c : denote_env pre ==> denote_env post)%triple.

Fixpoint sens_expr {t ts} (ctx : @env ts) (e : expr t ts) : Z.
Admitted.

Lemma assign_sound :
  forall {t ts} (ctx : @env ts) (x : var t ts) (e : expr t ts) d,
    sens_expr ctx e = d ->
    ([x <- e] ~_(0%R) [x <- e] : denote_env ctx ==> denote_env (env_update ctx x d))%triple.
(* Use aprhl_assign *)
Admitted.

End TypeSystem.
