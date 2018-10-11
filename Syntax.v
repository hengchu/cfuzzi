Require Export Coq.Strings.String.
Require Export ZArith.
Require Export Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Export Cfuzzi.BaseDefinitions.

Inductive expr : Type :=
| e_lit : Z -> expr
| e_var : var -> expr
| e_add : expr -> expr -> expr
| e_minus : expr -> expr -> expr
| e_mult : expr -> expr -> expr
| e_div : expr -> expr -> expr
| e_lt : expr -> expr -> expr
| e_eq : expr -> expr -> expr
| e_and : expr -> expr -> expr
| e_or : expr -> expr -> expr
| e_index : expr -> expr -> expr
| e_length : expr -> expr.

Fixpoint fvs (e: expr) : list var :=
  match e with
  | e_lit _ => []
  | e_var x => [x]
  | e_add e1 e2 => (fvs e1) ++ (fvs e2)
  | e_minus e1 e2 => (fvs e1) ++ (fvs e2)
  | e_mult e1 e2 => (fvs e1) ++ (fvs e2)
  | e_div e1 e2 => (fvs e1) ++ (fvs e2)
  | e_lt e1 e2 => (fvs e1) ++ (fvs e2)
  | e_eq e1 e2 => (fvs e1) ++ (fvs e2)
  | e_and e1 e2 => (fvs e1) ++ (fvs e2)
  | e_or e1 e2 => (fvs e1) ++ (fvs e2)
  | e_index e1 e2 => (fvs e1) ++ (fvs e2)
  | e_length e => fvs e
  end.

Coercion e_var : var >-> expr.
Coercion e_lit : Z >-> expr.

Ltac prune_eqdec_cases :=
  try (solve [right; intros contra; exfalso; inversion contra; auto]).

Lemma expr_eqdec : forall e1 e2 : expr,
    {e1 = e2} + {e1 <> e2}.
Proof.
  induction e1.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (Z.eq_dec z z0).
    + left; subst; auto.
    + right; intros contra; inversion contra; exfalso; apply n; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (var_eqdec v v0).
    + left; subst; auto.
    + right; intros contra; inversion contra; exfalso; apply n; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1_1 e2_1);
      destruct (IHe1_2 e2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
  - intros e2; destruct e2; prune_eqdec_cases.
    destruct (IHe1 e2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + left; subst; auto.
Defined.

Definition ev := e_var.
Definition el := e_lit.

Notation "e1 ':+' e2" := (e_add e1 e2) (at level 65, left associativity) : expr_scope.
Notation "e1 ':-' e2" := (e_minus e1 e2) (at level 65, left associativity) : expr_scope.
Notation "e1 ':*' e2" := (e_mult e1 e2) (at level 64, left associativity) : expr_scope.
Notation "e1 ':/' e2" := (e_div e1 e2) (at level 64, left associativity) : expr_scope.
Notation "e1 ':<' e2" := (e_lt e1 e2) (at level 68, no associativity) : expr_scope.
Notation "e1 ':==' e2" := (e_eq e1 e2) (at level 69, no associativity) : expr_scope.
Notation "e1 ':&&' e2" := (e_and e1 e2) (at level 66, left associativity) : expr_scope.
Notation "e1 ':||' e2" := (e_or e1 e2) (at level 67, left associativity) : expr_scope.
Notation "e1 '!!' e2" := (e_index e1 e2) (at level 63, no associativity) : expr_scope.
Notation "'len(' e ')'" := (e_length e) (at level 63) : expr_scope.

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.

Module TestNotations.
Parameter x : var.
Parameter y : var.
Parameter z : var.

Check (x :+ y :- x :* x)%expr.
Check (x :< y)%expr.
Check (z :&& z)%expr.
Check (x :+ y :< y :* y)%expr.
Check (1%Z :< x :+ y)%expr.
End TestNotations.

Inductive base_instr : Type :=
| bi_assign : var -> expr -> base_instr
| bi_laplace : var
               -> positive (* width *)
               -> expr
               -> base_instr
| bi_index_assign : var -> expr -> expr -> base_instr
| bi_length_assign : var -> expr -> base_instr.

Lemma base_instr_eqdec : forall b1 b2 : base_instr,
    {b1 = b2} + {b1 <> b2}.
Proof.
  induction b1.
  - intros b2.
    destruct b2; prune_eqdec_cases.
    destruct (var_eqdec v v0);
      destruct (expr_eqdec e e0);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; left; auto.
  - intros b2.
    destruct b2; prune_eqdec_cases.
    destruct (var_eqdec v v0);
      destruct (Pos.eq_dec p p0);
      destruct (expr_eqdec e e0);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; left; auto.
  - intros b2.
    destruct b2; prune_eqdec_cases.
    destruct (var_eqdec v v0);
      destruct (expr_eqdec e e1);
      destruct (expr_eqdec e0 e2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    subst; left; auto.
  - intros b2.
    destruct b2; prune_eqdec_cases.
    destruct (var_eqdec v v0);
      destruct (expr_eqdec e e0);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; auto.
Defined.

Inductive cmd : Type :=
| i_skip : cmd
| i_base_instr : base_instr -> cmd
| i_cond : expr -> cmd -> cmd -> cmd
| i_while : expr -> cmd -> cmd
| i_seq : cmd -> cmd -> cmd.

Fixpoint mvs (c: cmd) : list var :=
  match c with
  | i_skip => []
  | i_base_instr bi =>
    match bi with
    | bi_assign x _ => [x]
    | bi_laplace x _ _ => [x]
    | bi_index_assign x _ _ => [x]
    | bi_length_assign x _ => [x]
    end
  | i_cond _ c1 c2 =>
    mvs c1 ++ mvs c2
  | i_while _ c =>
    mvs c
  | i_seq c1 c2 =>
    mvs c1 ++ mvs c2
  end.

Lemma cmd_eqdec : forall c1 c2: cmd,
    {c1 = c2} + {c1 <> c2}.
Proof.
  induction c1.
  - intros c2; destruct c2; prune_eqdec_cases.
    auto.
  - intros c2; destruct c2; prune_eqdec_cases.
    destruct (base_instr_eqdec b b0);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; auto.
  - intros c2; destruct c2; prune_eqdec_cases.
    destruct (expr_eqdec e e0);
      destruct (IHc1_1 c2_1);
      destruct (IHc1_2 c2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; auto.
  - intros c2; destruct c2; prune_eqdec_cases.
    destruct (expr_eqdec e e0);
      destruct (IHc1 c2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; auto.
  - intros c2; destruct c2; prune_eqdec_cases.
    destruct (IHc1_1 c2_1);
      destruct (IHc1_2 c2_2);
      try (solve [right; intros contra; inversion contra; subst; clear contra;
                  apply n; auto]).
    + subst; auto.
Defined.

Notation "'If' e 'then' c1 'else' c2 'end'" := (i_cond e c1 c2) (at level 75) : cmd_scope.
Notation "'If' e 'then_' c 'end'" := (i_cond e c i_skip) (at level 75) : cmd_scope.
Notation "'While' e 'do' c 'end'" := (i_while e c) (at level 75) : cmd_scope.
Notation "'at(' x ',' e1 ')' '<-' e2" := (i_base_instr (bi_index_assign x e1 e2)) (at level 75) : cmd_scope.
Notation "'len(' x ')' '<-' e" := (i_base_instr (bi_length_assign x e)) (at level 75) : cmd_scope.
Notation "x '<-' e" := (i_base_instr (bi_assign x e)) (at level 75) : cmd_scope.
Notation "x '<$-' 'lap(' w ',' e ')'" := (i_base_instr (bi_laplace x w e)) (at level 75) : cmd_scope.
Notation "c1 ';;' c2" := (i_seq c1 c2) (at level 75, right associativity) : cmd_scope.

Bind Scope cmd_scope with cmd.
Delimit Scope cmd_scope with cmd.
