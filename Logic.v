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

Definition proj_left {ts} (d : distr (memory ts * memory ts)) := Mlet d (fun pm => Munit (fst pm)).
Definition proj_right {ts} (d : distr (memory ts * memory ts)) := Mlet d (fun pm => Munit (snd pm)).

Definition memory_relation ts := memory ts -> memory ts -> Prop.

Definition support_cond
           {ts}
           (m : distr ((memory ts) * (memory ts)))
           (R : memory_relation ts) :=
  range (fun pm => R (fst pm) (snd pm)) m.

Definition mem_eqdec {ts} : forall (m1 m2 : memory ts), {m1 = m2} + {m1 <> m2} :=
  @h_eqdec _ _ tau_denote_eqdec ts.

Definition mem_pair_eqdec {ts} : forall (pm1 pm2 : (memory ts) * (memory ts)),
    {pm1 = pm2} + {pm1 <> pm2}.
  refine (fun pm1 pm2 =>
            match pm1, pm2 with
            | (m1, m2), (m3, m4)
              => match (mem_eqdec m1 m3), (mem_eqdec m2 m4) with
                | left pf1, left pf2 => left _
                | _, _ => right _
                end
            end).
  - subst; auto.
  - intros contra. inversion contra; subst. apply n; auto.
  - intros contra. inversion contra; subst. apply n; auto.
Defined.

(* https://justinh.su/files/slides/approx-couplings.pdf, page 23 *)
Definition approximate_lifting
           {ts}
           {eps : R}
           (eps_gt_0 : (eps >= 0)%R)
           (Q : memory_relation ts)
           (m1 m2 : distr (memory ts)) :=
  exists (u_l u_r : distr ((memory ts) * (memory ts))),
    eq_distr (proj_left u_l) m1
    /\ eq_distr (proj_right u_r) m2
    /\ support_cond u_l Q
    /\ support_cond u_r Q
    /\ forall pm,
        ((iR (mu u_l (carac (mem_pair_eqdec pm))))
         <= (exp eps) * iR (mu u_r (carac (mem_pair_eqdec pm))))%R.

Definition triple
           {ts}
           (eps : R)
           (P : memory_relation ts)
           (c1 c2 : cmd ts)
           (Q : memory_relation ts) :=
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

Module Test.
Definition env := [t_int; t_bool; t_int]%list.
Parameter x : var t_int env.
Parameter y : var t_bool env.
Parameter z : var t_int env.
Check ([x <- el 1%Z] ~_(0%R) [x <- el 1%Z] : (fun _ _ => True) ==> (fun _ _ => True))%triple.
Check (([x <- ev x :+ ev z]) ~_(0%R) [x <- ev z :+ ev x] : (fun _ _ => True) ==> (fun _ _ => True))%triple.
End Test.

Search (positive -> Z).

Local Open Scope triple_scope.

Lemma aprhl_laplace :
  forall {ts} (w : positive) (x1 x2 : var t_int ts) (e1 e2 : expr t_int ts) d,
    [x1 <$- lap(w, e1)] ~_((IZR (Zpos w) * IZR d)%R) [x2 <$- lap(w, e2)] :
      (fun m1 m2 => (sem_expr m1 e1 - sem_expr m2 e2 <= d)%Z)
        ==> (fun m1 m2 => h_get m1 x1 = h_get m2 x2).
Proof.
  intros ts w x1 x2 e1 e2 d.
  unfold triple.
  intros m1 m2 m1' m2' H_eps.
  intros P.
  intros Hdeno1 Hdeno2.
  unfold approximate_lifting.
Admitted.

Definition assign_sub_left
           {t ts}
           (P : memory_relation ts)
           (x : var t ts)
           (a : tau_denote t) : memory_relation ts :=
  fun m1 =>
    fun m2 =>
      P (h_weak_update a m1 x) m2.

Definition assign_sub_right
           {t ts}
           (P : memory_relation ts)
           (x : var t ts)
           (a : tau_denote t) : memory_relation ts :=
  fun m1 =>
    fun m2 =>
      P m1 (h_weak_update a m2 x).

Notation "P 'L([' x |-> a '])'" := (assign_sub_left P x a) (at level 10).
Notation "P 'R([' x |-> a '])'" := (assign_sub_right P x a) (at level 10).

Lemma aprhl_assign:
  forall {t ts} (x1 x2 : var t ts) (e1 e2 : expr t ts) P,
    [x1 <- e1] ~_(0%R) [x2 <- e2] :
      (fun m1 m2 => P L([x1 |-> sem_expr m1 e1]) R([x2 |-> sem_expr m2 e2]) m1 m2)
        ==> P.
Proof.
  intros t ts x1 x2 e1 e2 P.
  unfold triple.
  intros m1 m2 m1' m2' H_eps Hpre Hdeno1 Hdeno2.
  unfold approximate_lifting.
Admitted.

Lemma aprhl_seq:
  forall {ts} (c1 c1' c2 c2': cmd ts) (P Q S : memory_relation ts) (eps eps' : R),
    c1 ~_(eps) c1' : P ==> Q ->
    c2 ~_(eps') c2' : Q ==> S ->
    (c1 ++ c2) ~_((eps + eps')%R) (c1' ++ c2') : P ==> S.
Proof.
Admitted.

Lemma aprhl_cond:
  forall {ts} (e1 e2 : expr t_bool ts) (ct1 ct2 cf1 cf2 : cmd ts) (P Q : memory_relation ts) (eps : R),
    forall m1 m2, P m1 m2 -> (sem_expr m1 e1 = sem_expr m2 e2) ->
    ct1 ~_(eps) ct2 : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = true) ==> Q ->
    cf1 ~_(eps) cf2 : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = false) ==> Q ->
    ([If e1 then ct1 else cf1 end]%list) ~_(eps) ([If e2 then ct2 else cf2 end]%list) : P ==> Q.
Proof.
Admitted.

Lemma aprhl_while0:
  forall {ts} (e1 e2 : expr t_bool ts) (c1 c2 : cmd ts) (Pinv : memory_relation ts),
    forall m1 m2, Pinv m1 m2 -> (sem_expr m1 e1 = sem_expr m2 e2) ->
    c1 ~_(0%R) c2 : (fun m1 m2 => Pinv m1 m2 /\ sem_expr m1 e1 = true) ==> Pinv ->
    ([While e1 do c1 end]%list) ~_(0%R) ([While e2 do c2 end]%list)
      : Pinv ==> (fun m1 m2 => Pinv m1 m2 /\ sem_expr m1 e1 = false).
Proof.
Admitted.

Lemma aprhl_while:
  forall {ts}
         (e1 e2 : expr t_bool ts)
         (ev : expr t_int ts)
         (c1 c2 : cmd ts)
         (P : memory_relation ts)
         (eps : R)
         (N : nat),
  forall m1 m2, (P m1 m2 /\ (sem_expr m1 ev <= 0)%Z -> sem_expr m1 e1 = false) ->
  forall m1 m2, (P m1 m2 -> sem_expr m1 e1 = sem_expr m2 e2) ->
  forall (k : nat),
    c1 ~_(eps) c2
    : (fun m1 m2 =>
         P m1 m2
         /\ sem_expr m1 e1 = true
         /\ sem_expr m1 ev = Z.of_nat k)
        ==> (fun m1 m2 =>
               P m1 m2
               /\ (sem_expr m1 ev < Z.of_nat k)%Z) ->

      ([While e1 do c1 end]%list) ~_(((INR N) * eps)%R) ([While e2 do c2 end]%list) :

      (fun m1 m2 =>
         P m1 m2
         /\ (sem_expr m1 ev <= Z.of_nat N)%Z)
        ==> (fun m1 m2 =>
               P m1 m2
               /\ sem_expr m1 e1 = false).
Proof.
Admitted.

Lemma aprhl_conseq:
  forall {ts}
    c1 c2 (P P' Q' Q : memory_relation ts) eps' eps,
  c1 ~_(eps') c2 : P' ==> Q' ->
  (forall m1 m2, P m1 m2 -> P' m1 m2) ->
  (forall m1 m2, Q' m1 m2 -> Q m1 m2) ->
  (eps' <= eps)%R ->
  c1 ~_(eps) c2 : P ==> Q.
Proof.
Admitted.

Lemma aprhl_case:
  forall {ts}
    c1 c2 (P Q R : memory_relation ts) eps,
    (c1 ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ Q m1 m2) ==> R) ->
    (c1 ~_(eps) c2 : (fun m1 m2 => P m1 m2 /\ ~(Q m1 m2)) ==> R) ->
    c1 ~_(eps) c2 : P ==> R.
Proof.
Admitted.

Definition losslessP {ts} (P : memory ts -> Prop) (c : cmd ts) :=
  forall m, P m -> lossless c.

Lemma aprhl_while_L:
  forall {ts}
    e1 c1 (P : memory_relation ts) (P1 : memory ts -> Prop),
    (forall m1 m2, P m1 m2 -> P1 m1) ->
    losslessP P1 ([While e1 do c1 end]%list) ->
    (c1 ~_(0) [] : (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = true) ==> P) ->
    [While e1 do c1 end] ~_(0) [] : P ==> (fun m1 m2 => P m1 m2 /\ sem_expr m1 e1 = false).
Proof.
  Admitted.

Lemma aprhl_while_R:
  forall {ts}
    e2 c2 (P : memory_relation ts) (P2 : memory ts -> Prop),
    (forall m1 m2, P m1 m2 -> P2 m2) ->
    losslessP P2 ([While e2 do c2 end]%list) ->
    ([] ~_(0) c2 : (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = true) ==> P) ->
    [] ~_(0) [While e2 do c2 end] : P ==> (fun m1 m2 => P m1 m2 /\ sem_expr m2 e2 = false).
Proof.
Admitted.

Lemma aprhl_equiv:
  forall {ts}
    c1 c1' c2 c2' eps (P Q : memory_relation ts),
  (c1' ~_(eps) c2' : P ==> Q) ->
  (forall m, eq_distr ([[c1]] m) ([[c1']] m)) ->
  (forall m, eq_distr ([[c2]] m) ([[c2']] m)) ->
  c1 ~_(eps) c2 : P ==> Q.
Proof.
Admitted.

End APRHL.
