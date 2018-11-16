Require Import Coq.Lists.List.
Require Import Cfuzzi.Tactics.CpdtTactics.

Class Monad (m: Type -> Type) :=
  {
    ret: forall {A: Type}, A -> m A;
    bind: forall {A B: Type}, m A -> (A -> m B) -> m B
  }.


Notation "a '<--' ma ';;' f" := (bind ma f)
                                (at level 99,
                                 right associativity,
                                 format "'[v  ' '[' a '<--' ma ';;' ']' '/' '[' f ']' ']'") : Monad_scope.
Notation "ma '>>=' f" := (bind ma f) (at level 69, left associativity) : Monad_scope.
Bind Scope Monad_scope with Monad.
Delimit Scope Monad_scope with Monad.

Local Open Scope Monad_scope.

Class LawfulMonad (m: Type -> Type) `{Monad m} :=
  {
    left_id: forall {A B: Type} (f: A -> m B) (a: A),
      ret a >>= f = f a;
    right_id: forall {A: Type} (ma: m A),
        ma >>= ret = ma;
    assoc: forall {A B C: Type} (ma: m A) (f: A -> m B) (g: B -> m C),
        ma >>= f >>= g = ma >>= (fun x => f x >>= g)
  }.

Definition option_ret {A: Type} (a: A) := Some a.
Definition option_bind {A B: Type} (ma: option A) (f: A -> option B) :=
  match ma with
  | Some a => f a
  | None => None
  end.

Instance Monad_option: Monad option :=
  {
    ret := fun A a => @option_ret A a;
    bind := fun A B a f => @option_bind A B a f
  }.

Lemma option_left_id: forall {A B: Type} (f: A -> option B) a,
    ret a >>= f = f a.
Proof.
  intros A B f a.
  auto.
Qed.

Lemma option_right_id: forall {A: Type} (ma: option A),
    ma >>= ret = ma.
Proof.
  destruct ma; auto.
Qed.

Lemma option_assoc: forall {A B C: Type} (ma: option A) (f: A -> option B) (g: B -> option C),
    ma >>= f >>= g = ma >>= (fun x => f x >>= g).
Proof.
  destruct ma; auto.
Qed.

Program Instance LawfulMonad_option: LawfulMonad option.
Next Obligation.
  destruct ma; auto.
Qed.
Next Obligation.
  destruct ma; auto.
Qed.

Definition list_ret {A: Type} (a: A) := cons a nil.
Definition list_bind {A B: Type} (ma: list A) (f: A -> list B) :=
  concat (map f ma).

Instance Monad_list: Monad list :=
  {
    ret := fun A a => @list_ret A a;
    bind := fun A B a f => @list_bind A B a f
  }.

Local Hint Rewrite app_nil_r.
Local Hint Rewrite map_app.
Local Hint Rewrite concat_app.

Program Instance LawfulMonad_list: LawfulMonad list.
Next Obligation.
  unfold list_bind, list_ret.
  apply app_nil_r.
Qed.
Next Obligation.
  unfold list_bind.
  induction ma; crush.
Qed.
Next Obligation.
  unfold list_bind.
  induction ma; crush.
Qed.
