Require Export Coq.Classes.Morphisms.

Require Export Lib.
Require Export VariableDefinitions.
Require Export Syntax.
Require Export Hlist.

Require Export Program.

Module Semantics (E : Embedding).

Module LAP := Laplace(E).
Import E.
Import LAP.
Import LAP.RP.
Import LAP.RP.PP.
Import LAP.RP.PP.MP.
Import LAP.RP.PP.MP.UP.

Definition memory (ts : list tau) := hlist tau tau_denote ts.
Definition mem_get {t ts} (m : memory ts) (x : var t ts) : tau_denote t := h_get m x.
Definition mem_set {t ts} (m : memory ts) (x : var t ts) (v : tau_denote t) : memory ts :=
  h_weak_update v m x.

Program Fixpoint sem_expr
        {t : tau}
        {ts : list tau}
        (m : memory ts) (e : expr t ts) : tau_denote t :=
  match e with
  | e_lit _ v => v
  | e_var _ _ x => mem_get m x
  | e_add _ e1 e2 => (sem_expr m e1 + sem_expr m e2)%Z
  | e_minus _ e1 e2 => (sem_expr m e1 - sem_expr m e2)%Z
  | e_mult _ e1 e2 => (sem_expr m e1 * sem_expr m e2)%Z
  | e_div _ e1 e2 => (sem_expr m e1 / sem_expr m e2)%Z
  | e_lt _ e1 e2 => (sem_expr m e1 <? sem_expr m e2)%Z
  | e_eq _ e1 e2 => (sem_expr m e1 =? sem_expr m e2)%Z
  | e_and _ e1 e2 => andb (sem_expr m e1) (sem_expr m e2)
  | e_or _ e1 e2 => orb (sem_expr m e1) (sem_expr m e2)
  end.

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

Definition step_base_instr {ts} (m: memory ts) (c : base_instr ts)
  : distr (memory ts) :=
  match c in base_instr ts' return (memory ts' -> distr (memory ts')) with
  | bi_assign _ _ x e
    => fun m => Munit (mem_set m x (sem_expr m e))
  | bi_laplace _ x c e
    => fun m => Mlet (Laplace (IZR (Zpos c)) (IZR_Zpos_gt_0 c) (sem_expr m e))
                 (fun v => Munit (mem_set m x v))
  end m.

Definition step_cmd {ts} (c: cmd ts) (m: memory ts)
  : distr ((cmd ts) * (memory ts)).
  destruct c eqn:Hcmd.
  - apply (Munit ([]%list, m)).
  - destruct i eqn:Hinstr.
    + pose (m' := step_base_instr m b).
      apply (Mlet m' (fun m' => Munit (l, m'))).
    + destruct (sem_expr m e) eqn:Hcond.
      * pose (cs := (l0 ++ l)%list).
        apply (Munit (cs, m)).
      * pose (cs := (l1 ++ l)%list).
        apply (Munit (cs, m)).
    + destruct (sem_expr m e) eqn:Hguard.
      * pose (cs := (l0 ++ c)%list).
        apply (Munit (cs,  m)).
      * apply (Munit (l, m)).
Defined.

Fixpoint step_trans {ts} (c: cmd ts) (m: memory ts) (n : nat)
  : distr ((cmd ts) * (memory ts)) :=
  match n with
  | O => Munit (c, m)
  | S n' => Mlet (step_trans c m n') (fun cm => step_cmd (fst cm) (snd cm))
  end.

Definition final {ts} (c : cmd ts) : bool :=
  match c with
  | List.nil => true
  | _ => false
  end.

Definition Mdistr0 {A : Type} : M A := fun _ => 0.
Hint Unfold Mdistr0.

Definition distr0 {A : Type} : distr A.
  apply Build_distr with (mu := Mdistr0).
  - unfold stable_inv.
    intros f; unfold Mdistr0; simpl; auto.
  - unfold stable_plus.
    intros f g Hfg; unfold Mdistr0; simpl; auto.
  - unfold stable_mult.
    intros k f; unfold Mdistr0; simpl; auto.
  - unfold monotonic.
    intros f g Hfg; unfold Mdistr0; simpl; auto.
Defined.

Definition step_star {ts} (c: cmd ts) (m: memory ts) (n : nat)
  : distr (memory ts)%type :=
  Mlet (step_trans c m n)
       (fun cm =>
          match cm with
          | (c, m) => if final c then Munit m else distr0
          end).

Hint Unfold step_cmd.
Hint Unfold step_trans.
Hint Unfold step_star.

Lemma step_final : forall {ts} (c : cmd ts) m,
    final c = true -> step_cmd c m = Munit (List.nil, m).
Proof.
  intros ts c m Hfinal.
  destruct c; try reflexivity.
  simpl in Hfinal.
  inversion Hfinal.
Qed.

Lemma step_trans_final : forall {ts} (c : cmd ts) m n,
    final c = true -> eq_distr (step_trans c m n) (Munit (List.nil, m)).
Proof.
  intros ts c m n.
  generalize dependent ts.
  induction n.
  - intros ts c m Hfinal. simpl.
    destruct c; [auto | inversion Hfinal].
  - intros ts c m Hfinal. simpl.
    apply eq_distr_trans
      with (m2 := (Mlet (Munit (@List.nil (@instr ts), m)) (fun cm : (cmd ts) * memory ts => step_cmd (fst cm) (snd cm)))); auto.
    apply Mlet_compat; auto.
    rewrite Mlet_unit.
    simpl.
    reflexivity.
Qed.

Module Test.
Example x := m_first t_int List.nil.
Example m1 := @h_cons tau tau_denote t_int List.nil 1%Z h_nil.
Example m2 := @h_cons tau tau_denote t_int List.nil 0%Z h_nil.
Example prog1 :=
  [ While (e_lt (e_lit 0%Z) (e_var x)) do
          [ x <- e_minus (e_var x) (e_lit 1%Z) ]%list
    end ]%list.
Example prog2 :=
  [ x <$- lap(1%positive, e_var x) ]%list.
End Test.

Search "lub".

Lemma step_star_monotonic : forall {ts} (c : cmd ts) (m : memory ts) (j k: nat),
    (j <= k)%nat -> le_distr (step_star c m j) (step_star c m k).
Proof.
  intros ts c m j k Hjk.
  generalize dependent ts.
  induction Hjk as [|k Hle IH]; auto.
  - intros ts c m.
    apply le_distr_trans with (m2 := step_star c m k); auto.
    intros f.
    simpl.
    rewrite law3.
    apply mu_monotonic.
    unfold fle.
    intros [[|i1 c1] m1].
    + simpl. rewrite law1. simpl. auto.
    + replace (fst ((i1 :: c1)%list, m1)) with ((i1 :: c1)%list); auto.
Qed.

Definition deno {ts} (c : cmd ts) (m : memory ts) :=
  mu_lub (step_star c m) (step_star_monotonic c m).

Notation "'[[' c ']]'" := (deno c) (at level 65).

Module Test2.
  Import Test.
  Check ([[ prog1 ]]).
End Test2.

End Semantics.
