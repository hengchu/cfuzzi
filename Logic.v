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

Definition proj_left (d : distr (memory * memory)) := Mlet d (fun pm => Munit (fst pm)).
Definition proj_right (d : distr (memory * memory)) := Mlet d (fun pm => Munit (snd pm)).

Definition memory_relation := memory -> memory -> Prop.

Definition memory_eqb (m1 m2 : memory) :=
  VarMap.equal val_eqb m1 m2.

Definition memory_eqb2 (pm1 pm2 : (memory * memory)) :=
  andb (memory_eqb (fst pm1) (fst pm2))
       (memory_eqb (snd pm1) (snd pm2)).

Search distr.

Definition support_cond (m : distr (memory * memory)) (R : memory_relation) :=
  forall pm,
    (0 < (mu m (fun pm' => if memory_eqb2 pm' pm then 1%U else 0%U)))%U
    -> R (fst pm) (snd pm).

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
    /\ forall (pm : memory * memory),
        (iR (mu u_l (fun pm' => if memory_eqb2 pm pm' then 1%U else 0%U))
        <= (exp eps) * iR (mu u_r (fun pm' => if memory_eqb2 pm pm' then 1%U else 0%U)))%R.

Definition triple
           (eps : R)
           (P : memory_relation)
           (c1 c2 : cmd)
           (Q : memory_relation) :=
  forall m1 m2 m1' m2'
         (eps_gt_0 : (eps >= 0)%R),
    P m1 m2
    -> step_cmd (Munit m1) c1 m1'
    -> step_cmd (Munit m2) c2 m2'
    -> approximate_lifting eps_gt_0 Q m1' m2'.

Notation "c1 '~_(' eps ')' c2 ':' P '==>' Q" :=
  (triple eps P c1 c2 Q) (at level 65, c2 at level 64, P at level 50).

Check ([x <- 1%Z] ~_(0%R) [x <- 1%Z] : (fun _ _ => True) ==> (fun _ _ => True)).

End APRHL.
