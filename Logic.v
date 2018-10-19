Require Export Cfuzzi.Semantics.
Require Export Carac.
Require Import Coq.Reals.Reals.

Module Type APRHL(E: Embedding) (LAP: Laplace(E)).
  Module SEMImpl := Semantics.Make(E)(LAP).
  Import SEMImpl LAPImpl CARImpl RP PP MP UP EImpl.

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

  Parameter mem_pair_eqdec : forall (pm1 pm2 : memory * memory),
      {memory_Equal2 pm1 pm2} + {~(memory_Equal2 pm1 pm2)}.

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
             (stenv1 stenv2: st_env)
             (eps : R)
             (P : memory_relation)
             (c1 c2 : cmd)
             (Q : memory_relation) :=
    forall m1 m2 m1' m2'
      (eps_gt_0 : (eps >= 0)%R),
      P m1 m2
      -> welltyped_memory stenv1 m1
      -> welltyped_memory stenv2 m2
      -> m1' = [[ c1 ]] m1
      -> m2' = [[ c2 ]] m2
      -> approximate_lifting eps_gt_0 Q m1' m2'.

  Notation "env1 '⊕' env2 '|-' c1 '~_(' eps ')' c2 ':' P '==>' Q" :=
    (triple env1 env2 eps P c1 c2 Q) (at level 65, c2 at level 64, P at level 50) : triple_scope.

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

  Parameter aprhl_laplace :
    forall (w : positive) (env : st_env) (x1 x2 : var) (e1 e2 : expr) d,
    VarMap.MapsTo x1 t_int env ->
    VarMap.MapsTo x2 t_int env ->
    welltyped_expr env e1 t_int ->
    welltyped_expr env e2 t_int ->
    env ⊕ env |- (x1 <$- lap(w, e1)) ~_((IZR (Zpos w) * IZR d)%R) (x2 <$- lap(w, e2)) :
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

  Definition some_value (m: memory) (e: expr) :=
    exists v, sem_expr m e = Some v.

  Definition assign_sub_left
            (P : memory_relation)
            (x : var)
            (e : expr) : memory_relation :=
    fun m1 =>
      fun m2 =>
        some_value m1 e ->
        match sem_expr m1 e with
        | Some a =>
          P (mem_set x a m1) m2
        | None =>
          False
        end.

  Definition assign_sub_right
             (P : memory_relation)
             (x : var)
             (e : expr) : memory_relation :=
    fun m1 =>
      fun m2 =>
        some_value m2 e ->
        match sem_expr m2 e with
        | Some a =>
          P m1 (mem_set x a m2)
        | None =>
          False
        end.

  Notation "P 'L([' x |-> a '])'" := (assign_sub_left P x a) (at level 10).
  Notation "P 'R([' x |-> a '])'" := (assign_sub_right P x a) (at level 10).

  Definition some_int (m: memory) (e: expr) :=
    exists z, sem_expr m e = Some (v_int z).

  Definition some_arr_var (m: memory) (x: var) :=
    exists t arr, VarMap.find x m = Some (v_arr (t_arr t) arr).

  Definition assign_len_sub_left
             (P: memory_relation)
             (x: var)
             (e: expr): memory_relation :=
    fun m1 =>
      fun m2 =>
        some_int m1 e ->
        some_arr_var m1 x ->
        match sem_expr m1 e,
              VarMap.find x m1 with
        | Some (v_int z), Some (v_arr (t_arr t) arr) =>
          match val_arr_update_length t arr z with
          | Some varr'
            => P (mem_set x (v_arr (t_arr t) varr') m1) m2
          | None
            => False
          end
        | _, _ => False
        end.

  Definition assign_len_sub_right
             (P: memory_relation)
             (x: var)
             (e: expr): memory_relation :=
    fun m1 =>
      fun m2 =>
        some_int m2 e ->
        some_arr_var m2 x ->
        match sem_expr m2 e,
              VarMap.find x m2 with
        | Some (v_int z), Some (v_arr (t_arr t) arr) =>
          match val_arr_update_length t arr z with
          | Some varr'
            => P m1 (mem_set x (v_arr (t_arr t) varr') m2)
          | None
            => False
          end
        | _, _ => False
        end.

  Notation "P 'L([' 'len(' x ')' |-> a '])'" := (assign_len_sub_left P x a) (at level 10).
  Notation "P 'R([' 'len(' x ')' |-> a '])'" := (assign_len_sub_right P x a) (at level 10).

  Definition assign_index_sub_left
             (P: memory_relation)
             (x: var)
             (idx e: expr): memory_relation :=
    fun m1 =>
      fun m2 =>
        some_int m1 idx ->
        some_arr_var m1 x ->
        some_value m1 e ->
        match sem_expr m1 idx,
              sem_expr m1 e,
              VarMap.find x m1 with
        | Some (v_int z),
          Some v,
          Some (v_arr t arr) =>
          match val_arr_update arr z v with
          | Some varr' =>
            P (mem_set x (v_arr t varr') m1) m2
          | _ => False
          end
        | _, _, _ => False
        end.

    Definition assign_index_sub_right
             (P: memory_relation)
             (x: var)
             (idx e: expr): memory_relation :=
    fun m1 =>
      fun m2 =>
        some_int m2 idx ->
        some_arr_var m2 x ->
        some_value m2 e ->
        match sem_expr m2 idx,
              sem_expr m2 e,
              VarMap.find x m2 with
        | Some (v_int z),
          Some v,
          Some (v_arr t arr) =>
          match val_arr_update arr z v with
          | Some varr' =>
            P m1 (mem_set x (v_arr t varr') m2)
          | _ => False
          end
        | _, _, _ => False
        end.

  Notation "P 'L([' 'at(' x ',' idx ')' |-> a '])'" := (assign_index_sub_left P x idx a) (at level 10).
  Notation "P 'R([' 'at(' x ',' idx ')' |-> a '])'" := (assign_index_sub_right P x idx a) (at level 10).

  Parameter aprhl_skip:
    forall (env1 env2: st_env) P,
      env1 ⊕ env2 |- i_skip ~_(0%R) i_skip: P ==> P.

  Parameter aprhl_assign:
    forall (env1 env2 : st_env) (x1 x2 : var) (e1 e2 : expr) P,
      welltyped env1 (x1 <- e1)%cmd ->
      welltyped env2 (x2 <- e2)%cmd ->
      env1 ⊕ env2 |- (x1 <- e1) ~_(0%R) (x2 <- e2) :
        P L([x1 |-> e1]) R([x2 |-> e2]) ==> P.

  Parameter aprhl_len_assign:
    forall (env1 env2: st_env) (x1 x2: var) (e1 e2: expr) P,
      welltyped env1 (len(x1) <- e1)%cmd ->
      welltyped env2 (len(x2) <- e2)%cmd ->
      env1 ⊕ env2 |- (len(x1) <- e1) ~_(0%R) (len(x2) <- e2) :
       P L([len(x1) |-> e1]) R([len(x2) |-> e2]) ==> P.

  Parameter aprhl_index_assign:
    forall (env1 env2: st_env) (x1 x2: var) (idx1 idx2: expr) (e1 e2: expr) P,
      welltyped env1 (at(x1, idx1) <- e1)%cmd ->
      welltyped env2 (at(x2, idx2) <- e2)%cmd ->
      env1 ⊕ env2 |- (at(x1, idx1) <- e1) ~_(0%R) (at(x2, idx2) <- e2) :
        P L([at(x1, idx1) |-> e1]) R([at(x2, idx2) |-> e2]) ==> P.

  Parameter aprhl_seq:
    forall (env env': st_env) (c1 c1' c2 c2': cmd) (P Q S : memory_relation) (eps eps' : R),
      welltyped env c1 ->
      welltyped env' c1' ->
      welltyped env c2 ->
      welltyped env' c2' ->
      env ⊕ env' |- c1 ~_(eps) c1' : P ==> Q ->
      env ⊕ env' |- c2 ~_(eps') c2' : Q ==> S ->
      env ⊕ env' |- (c1 ;; c2) ~_((eps + eps')%R) (c1' ;; c2') : P ==> S.

  Parameter aprhl_cond:
    forall (env1 env2 : st_env)
      (e1 e2 : expr)
      (ct1 ct2 cf1 cf2 : cmd)
      (P Q : memory_relation) (eps : R),
      welltyped env1 (If e1 then ct1 else cf1 end)%cmd ->
      welltyped env1 (If e2 then ct2 else cf2 end)%cmd ->
      (forall m1 m2, welltyped_memory env1 m1
                -> welltyped_memory env2 m2
                -> P m1 m2
                -> sem_expr m1 e1 = sem_expr m2 e2) ->
      env1 ⊕ env2 |- ct1 ~_(eps) ct2 : (fun m1 m2 => P m1 m2
                                   /\ sem_expr m1 e1 = Some (v_bool true)) ==> Q ->
      env1 ⊕ env2 |- cf1 ~_(eps) cf2 : (fun m1 m2 => P m1 m2
                                   /\ sem_expr m1 e1 = Some (v_bool false)) ==> Q ->
      env1 ⊕ env2 |- (If e1 then ct1 else cf1 end) ~_(eps) (If e2 then ct2 else cf2 end) : P ==> Q.

  Parameter aprhl_while0:
    forall (env1 env2:st_env)
      (e1 e2 : expr)
      (c1 c2 : cmd)
      (Pinv : memory_relation),
      welltyped env1 (While e1 do c1 end)%cmd ->
      welltyped env2 (While e2 do c2 end)%cmd ->
      (forall m1 m2, welltyped_memory env1 m1
                -> welltyped_memory env2 m2
                -> Pinv m1 m2 -> (sem_expr m1 e1 = sem_expr m2 e2)) ->
      env1 ⊕ env2 |- c1 ~_(0%R) c2 : (fun m1 m2 => Pinv m1 m2
                                 /\ sem_expr m1 e1 = Some (v_bool true)) ==> Pinv ->
      env1 ⊕ env2 |- (While e1 do c1 end) ~_(0%R) (While e2 do c2 end)
        : Pinv ==> (fun m1 m2 => Pinv m1 m2 /\ sem_expr m1 e1 = (Some (v_bool false))).

Parameter aprhl_while:
  forall (env1 env2 : st_env)
    (e1 e2 : expr)
    (ev : expr)
    (c1 c2 : cmd)
    (P : memory_relation)
    (eps : R)
    (N : nat),
    welltyped env1 (While e1 do c1 end)%cmd ->
    welltyped env2 (While e2 do c2 end)%cmd ->
    (forall m1 m2, P m1 m2 /\ (lift_option_v_int_prop (fun v => v <= 0)%Z (sem_expr m1 ev))
              -> sem_expr m1 e1 = Some (v_bool false)) ->
    (forall m1 m2, P m1 m2
              -> sem_expr m1 e1 = sem_expr m2 e2) ->
    forall (k : nat),
      env1 ⊕ env2 |- c1 ~_(eps) c2
      : (fun m1 m2 =>
           P m1 m2
           /\ sem_expr m1 e1 = Some (v_bool true)
           /\ sem_expr m1 ev = Some (v_int (Z.of_nat k)))
          ==> (fun m1 m2 =>
               P m1 m2
               /\ (lift_option_v_int_prop (fun v => v <= Z.of_nat k)%Z (sem_expr m1 ev))) ->

        env1 ⊕ env2 |- (While e1 do c1 end) ~_(((INR N) * eps)%R) (While e2 do c2 end) :

        (fun m1 m2 =>
           P m1 m2
           /\ (lift_option_v_int_prop (fun v => v <= Z.of_nat N)%Z (sem_expr m1 ev)))
          ==> (fun m1 m2 =>
               P m1 m2
               /\ sem_expr m1 e1 = Some (v_bool false)).

Parameter aprhl_conseq:
  forall (env1 env2 : st_env) c1 c2 (P P' Q' Q : memory_relation) eps' eps,
    welltyped env1 c1 ->
    welltyped env2 c2 ->
  env1 ⊕ env2 |- c1 ~_(eps') c2 : P' ==> Q' ->
  (forall m1 m2, welltyped_memory env1 m1 -> welltyped_memory env2 m2 -> P m1 m2 -> P' m1 m2) ->
  (forall m1 m2, welltyped_memory env1 m1 -> welltyped_memory env2 m2 -> Q' m1 m2 -> Q m1 m2) ->
  (eps' <= eps)%R ->
  env1 ⊕ env2 |- c1 ~_(eps) c2 : P ==> Q.

Parameter aprhl_case:
  forall (env1 env2: st_env) c1 c2 (P Q R : memory_relation) eps,
    welltyped env1 c1 ->
    welltyped env2 c2 ->
    env1 ⊕ env2 |- c1 ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ Q m1 m2) ==> R ->
    env1 ⊕ env2 |- c1 ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ ~(Q m1 m2)) ==> R ->
    env1 ⊕ env2 |- c1 ~_(eps) c2 : P ==> R.

Definition losslessP (P : memory -> Prop) (c : cmd) :=
  forall m, P m -> lossless c.

Parameter aprhl_while_L:
  forall (env1 : st_env) e1 c1 (P : memory_relation) (P1 : memory -> Prop),
    welltyped env1 (While e1 do c1 end)%cmd ->
    (forall m1 m2, P m1 m2 -> P1 m1) ->
    losslessP P1 (While e1 do c1 end) ->
    env1 ⊕ env1 |- c1 ~_(0) i_skip
     : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool true)) ==> P ->
    env1 ⊕ env1 |- (While e1 do c1 end) ~_(0) i_skip
    : P ==> (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool false)).

Parameter aprhl_while_R:
  forall (env2 : st_env) e2 c2 (P : memory_relation) (P2 : memory -> Prop),
    welltyped env2 (While e2 do c2 end)%cmd ->
    (forall m1 m2, P m1 m2 -> P2 m2) ->
    losslessP P2 (While e2 do c2 end) ->
    env2 ⊕ env2 |- i_skip ~_(0) c2
     : (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = Some (v_bool true)) ==> P ->
    env2 ⊕ env2 |- i_skip ~_(0) (While e2 do c2 end)
    : P ==> (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = Some (v_bool false)).

Parameter aprhl_cond_L:
  forall (env1 env2: st_env) e1 c1t c1f c2 eps (P Q: memory_relation),
    welltyped env1 (If e1 then c1t else c1f end)%cmd ->
    welltyped env2 c2 ->
    (env1 ⊕ env2 |- c1t ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool true))
                                      ==> Q)%triple ->
    (env1 ⊕ env2 |- c1f ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = Some (v_bool false))
                                      ==> Q)%triple ->
    (env1 ⊕ env2 |- (If e1 then c1t else c1f end) ~_(eps) c2 : P ==> Q)%triple.

Parameter aprhl_cond_R:
  forall (env1 env2: st_env) c1 e2 c2t c2f eps (P Q: memory_relation),
    welltyped env1 c1 ->
    welltyped env2 (If e2 then c2t else c2f end) ->
    (env1 ⊕ env2 |- c1 ~_(eps) c2t : (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = Some (v_bool true))
                                      ==> Q)%triple ->
    (env1 ⊕ env2 |- c1 ~_(eps) c2f : (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = Some (v_bool false))
                                      ==> Q)%triple ->
    (env1 ⊕ env2 |- c1 ~_(eps) (If e2 then c2t else c2f end) : P ==> Q)%triple.

Parameter aprhl_equiv:
  forall (env1 env2: st_env) c1 c1' c2 c2' eps (P Q : memory_relation),
    welltyped env1 c1 ->
    welltyped env1 c1' ->
    welltyped env2 c2 ->
    welltyped env2 c2' ->
  env1 ⊕ env2 |- c1' ~_(eps) c2' : P ==> Q ->
  (forall m, eq_distr ([[c1]] m) ([[c1']] m)) ->
  (forall m, eq_distr ([[c2]] m) ([[c2']] m)) ->
  env1 ⊕ env2 |- c1 ~_(eps) c2 : P ==> Q.

End APRHL.
