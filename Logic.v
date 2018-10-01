Require Export Semantics.
Require Export Carac.

Module APRHL(E : Embedding).
Module SEM := Semantics.Semantics(E).
Module CAR := CaracFun(E).

Import E.
Import SEM.
Import SEM.LAP.
Import SEM.LAP.RP.
Import SEM.LAP.RP.PP.
Import SEM.LAP.RP.PP.MP.
Import SEM.LAP.RP.PP.MP.UP.
Import CAR.

Definition proj_left (d : distr (memory  * memory)) := Mlet d (fun pm => Munit (fst pm)).
Definition proj_right (d : distr (memory  * memory)) := Mlet d (fun pm => Munit (snd pm)).

Definition memory_relation := memory -> memory -> Prop.

Definition support_cond
           (m : distr (memory * memory))
           (R : memory_relation) :=
  range (fun pm => R (fst pm) (snd pm)) m.

Definition mem_eqdec : forall (m1 m2 : memory), {VarMap.Equal m1 m2} + {~(VarMap.Equal m1 m2)} :=
  VarMap_Equal_dec val_eqdec.

Definition memory_Equal2 (pm1 pm2 : memory * memory) :=
  (VarMap.Equal (fst pm1) (fst pm2)) /\ (VarMap.Equal (snd pm1) (snd pm2)).

Definition mem_pair_eqdec : forall (pm1 pm2 : memory * memory),
    {memory_Equal2 pm1 pm2} + {~(memory_Equal2 pm1 pm2)}.
  refine (fun pm1 pm2 =>
            match pm1, pm2 with
            | (m1, m2), (m3, m4)
              => match (mem_eqdec m1 m3), (mem_eqdec m2 m4) with
                | left pf1, left pf2 => left _
                | _, _ => right _
                end
            end).
  - unfold memory_Equal2; split; auto.
  - intros contra. inversion contra; subst.
    simpl in *. rewrite H0 in n. apply n; reflexivity.
  - intros contra. inversion contra; subst.
    simpl in *. rewrite H in n. apply n; reflexivity.
Defined.

(* https://justinh.su/files/slides/approx-couplings.pdf, page 23 *)
Definition approximate_lifting
           {eps : R}
           (eps_gt_0 : (eps >= 0)%R)
           (Q : memory_relation)
           (m1 m2 : distr memory) :=
  exists (u_l u_r : distr (memory * memory)),
    eq_distr (proj_left u_l) m1
    /\ eq_distr (proj_right u_r) m2
    /\ support_cond u_l Q
    /\ support_cond u_r Q
    /\ forall pm,
        ((iR (mu u_l (carac (mem_pair_eqdec pm))))
         <= (exp eps) * iR (mu u_r (carac (mem_pair_eqdec pm))))%R.

Definition triple
           (eps : R)
           (P : memory_relation)
           (c1 c2 : cmd)
           (Q : memory_relation) :=
  forall m1 m2 m1' m2'
         (eps_gt_0 : (eps >= 0)%R),
    P m1 m2
    -> m1' = [[ c1 ]] m1
    -> m2' = [[ c2 ]] m2
    -> approximate_lifting eps_gt_0 Q m1' m2'.

Notation "c1 '~_(' eps ')' c2 ':' P '==>' Q" :=
  (triple eps P c1 c2 Q) (at level 65, c2 at level 64, P at level 50) : triple_scope.

Bind Scope triple_scope with triple.
Delimit Scope triple_scope with triple.

Local Open Scope triple_scope.

Definition lift_option_v_int_prop (f : Z -> Prop) : option val -> Prop :=
  fun oa =>
    match oa with
    | Some (v_int a) => f a
    | _ => False
    end.
Definition lift_option_v_int_prop2 (f : Z -> Z -> Prop) : option val -> option val -> Prop :=
  fun oa ob =>
    match oa, ob with
    | Some (v_int a), Some (v_int b) => f a b
    | _, _ => False
    end.

Lemma aprhl_laplace :
  forall (w : positive) (env : st_env) (x1 x2 : var) (e1 e2 : expr) d,
    VarMap.MapsTo x1 t_int env ->
    VarMap.MapsTo x2 t_int env ->
    welltyped_expr env e1 t_int ->
    welltyped_expr env e2 t_int ->
    (x1 <$- lap(w, e1)) ~_((IZR (Zpos w) * IZR d)%R) (x2 <$- lap(w, e2)) :
      (fun m1 m2 =>
         (lift_option_v_int_prop2
            (fun v1 v2 => v1 - v2 <= d)%Z
            (sem_expr m1 e1)
            (sem_expr m2 e2)))
        ==>
        (fun m1 m2 =>
           lift_option_v_int_prop2
             (fun v1 v2 => v1 = v2)%Z
             (mem_get x1 m1)
             (mem_get x2 m2)).
Proof.
Admitted.

Definition assign_sub_left
           (P : memory_relation)
           (x : var)
           (a : option val) : memory_relation :=
  fun m1 =>
    fun m2 =>
      match a with
      | Some a =>
        P (mem_set x a m1) m2
      | None =>
        False
      end.

Definition assign_sub_right
           (P : memory_relation)
           (x : var)
           (a : option val) : memory_relation :=
  fun m1 =>
    fun m2 =>
      match a with
      | Some a =>
        P m1 (mem_set x a m2)
      | None =>
        False
      end.

Notation "P 'L([' x |-> a '])'" := (assign_sub_left P x a) (at level 10).
Notation "P 'R([' x |-> a '])'" := (assign_sub_right P x a) (at level 10).

Lemma aprhl_assign:
  forall (env1 env2 : st_env) (t1 t2 : tau) (x1 x2 : var) (e1 e2 : expr) P,
    VarMap.MapsTo x1 t1 env1 ->
    VarMap.MapsTo x2 t2 env2 ->
    welltyped_expr env1 e1 t1 ->
    welltyped_expr env2 e2 t2 ->
    (x1 <- e1) ~_(0%R) (x2 <- e2) :
      (fun m1 m2 => P L([x1 |-> sem_expr m1 e1]) R([x2 |-> sem_expr m2 e2]) m1 m2)
        ==> P.
Proof.
Admitted.

Lemma aprhl_seq:
  forall (env env': st_env) (c1 c1' c2 c2': cmd) (P Q S : memory_relation) (eps eps' : R),
    welltyped env c1 ->
    welltyped env' c1' ->
    welltyped env c2 ->
    welltyped env' c2' ->
    c1 ~_(eps) c1' : P ==> Q ->
    c2 ~_(eps') c2' : Q ==> S ->
    (c1 ;; c2) ~_((eps + eps')%R) (c1' ;; c2') : P ==> S.
Proof.
Admitted.

Lemma aprhl_cond:
  forall (env1 env2 : st_env)
    (e1 e2 : expr)
    (ct1 ct2 cf1 cf2 : cmd)
    (P Q : memory_relation) (eps : R),
    welltyped_expr env1 e1 t_bool ->
    welltyped_expr env2 e2 t_bool ->
    welltyped env1 ct1 ->
    welltyped env1 cf1 ->
    welltyped env2 ct2 ->
    welltyped env2 cf2 ->
    forall m1 m2, P m1 m2 -> (sem_expr m1 e1 = sem_expr m2 e2) ->
    ct1 ~_(eps) ct2 : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool true)) ==> Q ->
    cf1 ~_(eps) cf2 : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool false)) ==> Q ->
    (If e1 then ct1 else cf1 end) ~_(eps) (If e2 then ct2 else cf2 end) : P ==> Q.
Proof.
Admitted.

Lemma aprhl_while0:
  forall (env1 env2:st_env)
    (e1 e2 : expr)
    (c1 c2 : cmd)
    (Pinv : memory_relation),
    welltyped_expr env1 e1 t_bool ->
    welltyped_expr env2 e2 t_bool ->
    welltyped env1 c1 ->
    welltyped env2 c2 ->
    forall m1 m2, Pinv m1 m2 -> (sem_expr m1 e1 = sem_expr m2 e2) ->
    c1 ~_(0%R) c2 : (fun m1 m2 => Pinv m1 m2 /\ sem_expr m1 e1 = Some (v_bool true)) ==> Pinv ->
    (While e1 do c1 end) ~_(0%R) (While e2 do c2 end)
      : Pinv ==> (fun m1 m2 => Pinv m1 m2 /\ sem_expr m1 e1 = (Some (v_bool false))).
Proof.
Admitted.

Lemma aprhl_while:
  forall (env1 env2 : st_env)
    (e1 e2 : expr)
    (ev : expr)
    (c1 c2 : cmd)
    (P : memory_relation)
    (eps : R)
    (N : nat),
    welltyped_expr env1 e1 t_bool ->
    welltyped_expr env2 e2 t_bool ->
    welltyped env1 c1 ->
    welltyped env2 c2 ->
    (forall m1 m2, P m1 m2 /\ (lift_option_v_int_prop (fun v => v <= 0)%Z (sem_expr m1 ev))
              -> sem_expr m1 e1 = Some (v_bool false)) ->
    (forall m1 m2, P m1 m2
              -> sem_expr m1 e1 = sem_expr m2 e2) ->
    forall (k : nat),
      c1 ~_(eps) c2
      : (fun m1 m2 =>
           P m1 m2
           /\ sem_expr m1 e1 = Some (v_bool true)
           /\ sem_expr m1 ev = Some (v_int (Z.of_nat k)))
          ==> (fun m1 m2 =>
               P m1 m2
               /\ (lift_option_v_int_prop (fun v => v <= Z.of_nat k)%Z (sem_expr m1 ev))) ->

        (While e1 do c1 end) ~_(((INR N) * eps)%R) (While e2 do c2 end) :

        (fun m1 m2 =>
           P m1 m2
           /\ (lift_option_v_int_prop (fun v => v <= Z.of_nat N)%Z (sem_expr m1 ev)))
          ==> (fun m1 m2 =>
               P m1 m2
               /\ sem_expr m1 e1 = Some (v_bool false)).
Proof.
Admitted.

Lemma aprhl_conseq:
  forall (env1 env2 : st_env) c1 c2 (P P' Q' Q : memory_relation) eps' eps,
    welltyped env1 c1 ->
    welltyped env2 c2 ->
  c1 ~_(eps') c2 : P' ==> Q' ->
  (forall m1 m2, P m1 m2 -> P' m1 m2) ->
  (forall m1 m2, Q' m1 m2 -> Q m1 m2) ->
  (eps' <= eps)%R ->
  c1 ~_(eps) c2 : P ==> Q.
Proof.
Admitted.

Lemma aprhl_case:
  forall (env1 env2: st_env) c1 c2 (P Q R : memory_relation) eps,
    welltyped env1 c1 ->
    welltyped env2 c2 ->
    (c1 ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ Q m1 m2) ==> R) ->
    (c1 ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ ~(Q m1 m2)) ==> R) ->
    c1 ~_(eps) c2 : P ==> R.
Proof.
Admitted.

Definition losslessP (P : memory -> Prop) (c : cmd) :=
  forall m, P m -> lossless c.

Lemma aprhl_while_L:
  forall (env1 : st_env) e1 c1 (P : memory_relation) (P1 : memory -> Prop),
    welltyped_expr env1 e1 t_bool ->
    welltyped env1 c1 ->
    (forall m1 m2, P m1 m2 -> P1 m1) ->
    losslessP P1 (While e1 do c1 end) ->
    (c1 ~_(0) i_skip
     : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool true)) ==> P) ->
    (While e1 do c1 end) ~_(0) i_skip
    : P ==> (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool false)).
Proof.
  Admitted.

Lemma aprhl_while_R:
  forall (env2 : st_env) e2 c2 (P : memory_relation) (P2 : memory -> Prop),
    welltyped_expr env2 e2 t_bool ->
    welltyped env2 c2 ->
    (forall m1 m2, P m1 m2 -> P2 m2) ->
    losslessP P2 (While e2 do c2 end) ->
    (i_skip ~_(0) c2
     : (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = Some (v_bool true)) ==> P) ->
    i_skip ~_(0) (While e2 do c2 end)
    : P ==> (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = Some (v_bool false)).
Proof.
Admitted.

Lemma aprhl_equiv:
  forall (env1 env2: st_env) c1 c1' c2 c2' eps (P Q : memory_relation),
    welltyped env1 c1 ->
    welltyped env1 c1' ->
    welltyped env2 c2 ->
    welltyped env2 c2' ->
  (c1' ~_(eps) c2' : P ==> Q) ->
  (forall m, eq_distr ([[c1]] m) ([[c1']] m)) ->
  (forall m, eq_distr ([[c2]] m) ([[c2']] m)) ->
  c1 ~_(eps) c2 : P ==> Q.
Proof.
Admitted.

End APRHL.
