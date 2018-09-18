Require Import Coq.Program.Tactics.
Require Import Coq.Logic.JMeq.
Require Import Coq.Lists.List.
Require Import Program.
Require Import Coq.Program.Equality.
Require Import Coq.Logic.FunctionalExtensionality.

Section Hlist.

Variable A : Type.
Variable f : A -> Type.
Variable f_eqb : forall (x : A), f x -> f x -> bool.

Variable f_eqb_iff_eq : forall {x: A} (v1 v2 : f x),
    f_eqb x v1 v2 = true <-> v1 = v2.

Inductive hlist : list A -> Type :=
| h_nil : hlist nil
| h_cons : forall (x : A) (ls : list A), f x -> hlist ls -> hlist (x :: ls).

Variable elm : A.

Inductive member : list A -> Type :=
| m_first : forall ls, member (elm :: ls)
| m_next : forall x ls, member ls -> member (x :: ls).

Program Fixpoint h_get {ix : list A} (ls : hlist ix) : member ix -> f elm :=
  match ls with
  | h_nil => _
  | h_cons _ _ix2 v vs =>
    fun mem => match mem with
               | m_first _ => v
               | m_next _ _ mem' => @h_get _ix2 vs mem'
               end
  end.
Next Obligation.
  inversion X.
Defined.

Program Fixpoint h_weak_update {ix : list A} (new_v : f elm) (ls : hlist ix) {struct ls}
  : member ix -> hlist ix :=
      match ls with
      | h_nil =>
        fun _ => h_nil
      | h_cons _x _ix_tail old_v tl =>
        fun mem => match mem with
                   | m_first _ => h_cons _x _ix_tail new_v tl
                   | m_next _ _ mem' => h_cons _x _ix_tail old_v (@h_weak_update _ix_tail new_v tl mem')
                   end
      end.

Program Fixpoint h_eqb {ix : list A} (ls : hlist ix) {struct ls}
  : hlist ix -> bool :=
  match ls with
  | h_nil => fun _ => true
  | h_cons _ _ v tl => fun ls2 =>
                        match ls2 with
                        | h_nil => _
                        | h_cons _ _ v2 tl2 => andb (f_eqb _ v v2) (h_eqb tl tl2)
                        end
  end.

Lemma h_eqb_iff_eq : forall {ix} (ls1 ls2 : hlist ix),
    h_eqb ls1 ls2 = true <-> ls1 = ls2.
Proof.
  intros ix.
  induction ix.
  - intros ls1 ls2.
    split.
    + intros H_eqb.
      dependent destruction ls1.
      dependent destruction ls2.
      reflexivity.
    + intros Heq.
      subst.
      dependent destruction ls2.
      reflexivity.
  - intros ls1 ls2.
    split.
    + intros H_eqb.
      dependent destruction ls1;
        dependent destruction ls2.
      simpl in H_eqb.
      Search ((_ && _)%bool = true).
      apply Bool.andb_true_iff in H_eqb.
      destruct H_eqb as [Heq1 Heq2].
      apply IHix in Heq2.
      rewrite Heq2.
      f_equal.
      apply f_eqb_iff_eq; auto.
    + intros H_eq.
      subst.
      dependent destruction ls2.
      simpl. apply Bool.andb_true_iff.
      split.
      * apply f_eqb_iff_eq; auto.
      * apply IHix; auto.
Qed.

End Hlist.

Arguments h_nil   [_ _].
Arguments h_cons  [_ _ _ _] _ _.
Arguments member  [_] _ _.
Arguments m_first [_] _ _.
Arguments m_next  [_ _] _ [_] _.

Arguments h_get [_ _ _ _] _ _.
Arguments h_weak_update [_ _ _ _] _ _ _.
Arguments h_eqb [_ _] _ [_] _ _.

(* I don't think this is provable in Coq *)
Axiom member_inj : forall {A : Type} (elm1 elm2 : A) ls,
    member elm1 ls = member elm2 ls -> elm1 = elm2.

Lemma m_next_congr : forall {A : Type} elm1 elm2 x ls
                            (mem1 : @member A elm1 ls)
                            (mem2 : @member A elm2 ls),
    mem1 ~= mem2 -> m_next x mem1 ~= m_next x mem2.
Proof.
  intros A elm1 elm2 x ls mem1 mem2 Heq.
  dependent destruction Heq.
  assert (elm1 = elm2). {
    eapply member_inj; eauto.
  }
  subst.
  rewrite x.
  reflexivity.
Qed.

Fixpoint
  member_eq
  {A : Type}
  (teq : forall (t t': A), {t = t'} + {t <> t'})
  {t t' : A}
  {ts : list A}
  (m : member t ts)
  (m' : member t' ts)
  : {m ~= m'} + {~(m ~= m')}.
destruct (teq t t').
- subst.
  dependent destruction m;
    dependent destruction m'.
  + left. reflexivity.
  + right. intros contra. dependent destruction contra.
  + right. intros contra. dependent destruction contra.
  + destruct (member_eq A teq t' t' ls m m').
    * left. apply m_next_congr; auto.
    * right. intros contra. dependent destruction contra; auto.
- right. intros contra.
  dependent destruction contra.
  apply member_inj in x0.
  contradiction.
Defined.

Definition f (_ : nat) := nat.
Example hs : (hlist nat f nil) := h_nil.
Example hs1 : (hlist nat f (cons 0 (cons 1 nil))) := h_cons 1 (h_cons 2 h_nil).

Example mem1 := @m_first _ 0 (cons 1 nil).
Example mem2 := m_next 0 (m_first 1 nil).

Eval compute in (h_get hs1 (@m_first _ 0 (cons 1 nil))).
Eval compute in (h_weak_update 10 hs1 (@m_first _ 0 (cons 1 nil))).
Eval compute in (h_get hs1 mem2).
Eval compute in (h_weak_update 11 hs1 mem2).

Lemma elim_mem : forall {A : Type} elm x ls
                        (pf : @member A elm (x :: ls)),
    ((x = elm) /\ JMeq pf (m_first elm ls))
       \/ exists (pf2 : member elm ls), JMeq pf (m_next x pf2).
Proof.
  intros A elm x ls mem.
  dependent destruction mem.
  - left; auto.
  - right. exists mem. reflexivity.
Qed.

Lemma hlist_get_update_same : forall {A:Type} {f : A -> Type} {elm:A} {ix : list A} mem ls v,
    @h_get A f elm ix (h_weak_update v ls mem) mem = v.
Proof.
  intros A f elm ix mem.
  induction ls as [| _x _ls _fx _tl IH].
  - inversion mem.
  - intros v.
    dependent destruction mem.
    + simpl; reflexivity.
    + simpl; apply IH.
Qed.

Lemma hlist_get_update_different :
  forall {A : Type}
         {f : A -> Type}
         {elm1 elm2:A}
         {ix : list A}
         ls v1 v2
         (mem1 : member elm1 ix)
         (mem2 : member elm2 ix),
    ~(JMeq mem1 mem2)
    -> @h_get A f elm2 ix ls mem2 = v2
    -> @h_get A f elm2 ix (h_weak_update v1 ls mem1) mem2 = v2.
Proof.
  intros A f elm1 elm2 ix.
  dependent induction ls.
  - intros v1 v2 mem1; inversion mem1.
  - intros v1 v2 mem1 mem2 Hneq Hget2.
    destruct (elim_mem elm1 x ls mem1) as [Hfirst1 | Hnext1];
    destruct (elim_mem elm2 x ls mem2) as [Hfirst2 | Hnext2].
    + inversion Hfirst1; subst.
      inversion Hfirst2; subst.
      simpl.
      exfalso. apply Hneq; auto.
    + destruct Hnext2 as [_mem2 H_mem2_eq].
      inversion Hfirst1; subst.
      rewrite H0.
      simpl.
      reflexivity.
    + destruct Hnext1 as [_mem1  H_mem1_eq].
      inversion Hfirst2; subst.
      rewrite H0.
      simpl.
      reflexivity.
    + destruct Hnext1 as [_mem1 H_mem1_eq].
      destruct Hnext2 as [_mem2 H_mem2_eq].
      subst.
      simpl.
      apply IHls; auto.
      intros contra.
      apply Hneq.
      apply m_next_congr; auto.
Qed.
