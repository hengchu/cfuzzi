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

End APRHL.