Require Import Coq.Program.Tactics.
Require Import Coq.Logic.JMeq.
Require Import Coq.Lists.List.
Require Import Program.
Require Import Coq.Program.Equality.

Section Hlist.

Variable A : Type.
Variable f : A -> Type.

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
End Hlist.

Arguments h_nil   [_ _].
Arguments h_cons  [_ _ _ _] _ _.
Arguments member  [_] _ _.
Arguments m_first [_] _ _.
Arguments m_next  [_ _] _ [_] _.

Arguments h_get [_ _ _ _] _ _.
Arguments h_weak_update [_ _ _ _] _ _ _.

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

Lemma m_next_congr : forall {A : Type} elm x ls
                            (mem1 : @member A elm ls)
                            (mem2 : @member A elm ls),
    mem1 ~= mem2 -> m_next x mem1 ~= m_next x mem2.
Proof.
  intros A elm x ls mem1 mem2 Heq.
  rewrite Heq. reflexivity.
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
         {elm:A}
         {ix : list A}
         ls v1 v2
         (mem1 : member elm ix)
         (mem2 : member elm ix),
    ~(JMeq mem1 mem2)
    -> @h_get A f elm ix ls mem2 = v2
    -> @h_get A f elm ix (h_weak_update v1 ls mem1) mem2 = v2.
Proof.
  intros A f elm ix.
  dependent induction ls.
  - intros v1 v2 mem1; inversion mem1.
  - intros v1 v2 mem1 mem2 Hneq Hget2.
    destruct (elim_mem elm x ls mem1) as [Hfirst1 | Hnext1];
    destruct (elim_mem elm x ls mem2) as [Hfirst2 | Hnext2].
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
      rewrite contra.
      auto.
Qed.
