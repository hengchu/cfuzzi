Require Export Semantics.

Module APRHL(E : Embedding).
Module SEM := Semantics.Semantics(E).

Import E.
Import SEM.
Import SEM.LAP.
Import SEM.LAP.RP.
Import SEM.LAP.RP.PP.
Import SEM.LAP.RP.PP.MP.
Import SEM.LAP.RP.PP.MP.UP.

Definition proj_left {ts} (d : distr (memory ts * memory ts)) := Mlet d (fun pm => Munit (fst pm)).
Definition proj_right {ts} (d : distr (memory ts * memory ts)) := Mlet d (fun pm => Munit (snd pm)).

Definition memory_relation ts := memory ts -> memory ts -> Prop.

Definition memory_eqb {ts} (m1 m2 : memory ts) :=
  h_eqb tau_eqb m1 m2.

Definition memory_eqb2 {ts} (pm1 pm2 : ((memory ts) * (memory ts))) :=
  andb (memory_eqb (fst pm1) (fst pm2))
       (memory_eqb (snd pm1) (snd pm2)).

Definition support_cond {ts} (m : distr ((memory ts) * (memory ts))) (R : memory_relation ts) :=
  forall pm,
    (0 < (mu m (fun pm' => if memory_eqb2 pm' pm then 1%U else 0%U)))%U
    -> R (fst pm) (snd pm).

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
    /\ forall (pm : (memory ts) * (memory ts)),
        (iR (mu u_l (fun pm' => if memory_eqb2 pm pm' then 1%U else 0%U))
        <= (exp eps) * iR (mu u_r (fun pm' => if memory_eqb2 pm pm' then 1%U else 0%U)))%R.

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
  (triple eps P c1 c2 Q) (at level 65, c2 at level 64, P at level 50).

Module Test.
  Local Open Scope expr_scope.
Definition env := [t_int; t_bool; t_int]%list.
Parameter x : var t_int env.
Parameter y : var t_bool env.
Parameter z : var t_int env.
Check ([x <- el 1%Z] ~_(0%R) [x <- el 1%Z] : (fun _ _ => True) ==> (fun _ _ => True)).
Check ([x <- ev x :+ ev z]) ~_(0%R) [x <- ev z :+ ev x] : (fun _ _ => True) ==> (fun _ _ => True).
End Test.

Search (positive -> Z).

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

End APRHL.
