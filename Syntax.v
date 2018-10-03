Require Export Coq.Strings.String.
Require Export ZArith.
Require Export Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Export VariableDefinitions.

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
Notation "e1 '[' e2 ']'" := (e_index e1 e2) (at level 63, no associativity) : expr_scope.
Notation "'len(' e ')'" := (e_length e) (at level 63) : expr_scope.

Bind Scope expr_scope with expr.
Delimit Scope expr_scope with expr.

Module TestNotations.
Parameter x : var.
Parameter y : var.
Parameter z : var.

Check (ev x :+ ev y :- ev x :* ev x)%expr.
Check (ev x :< ev y)%expr.
Check (ev z :&& ev z)%expr.
Check (ev x :+ ev y :< ev y :* ev y)%expr.
Check (el 1%Z :< ev x :+ ev y)%expr.
End TestNotations.

Inductive base_instr : Type :=
| bi_assign : var -> expr -> base_instr
| bi_laplace : var
               -> positive (* width *)
               -> expr
               -> base_instr
| bi_index_assign : var -> expr -> expr -> base_instr
| bi_length_assign : var -> expr -> base_instr.

Inductive cmd : Type :=
| i_skip : cmd
| i_base_instr : base_instr -> cmd
| i_cond : expr -> cmd -> cmd -> cmd
| i_while : expr -> cmd -> cmd
| i_seq : cmd -> cmd -> cmd.

Lemma cmd_eqdec : forall c1 c2: cmd,
    {c1 = c2} + {c1 <> c2}.
Proof.
  (* Easy *)
Admitted.

Notation "'If' e 'then' c1 'else' c2 'end'" := (i_cond e c1 c2) (at level 75).
Notation "'If' e 'then_' c 'end'" := (i_cond e c nil) (at level 75).
Notation "'While' e 'do' c 'end'" := (i_while e c) (at level 75).
Notation "x '[' e1 ']' '<-' e2" := (i_base_instr (bi_index_assign x e1 e2)) (at level 75).
Notation "'len(' x ')' '<-' e" := (i_base_instr (bi_length_assign x e)) (at level 75).
Notation "x '<-' e" := (i_base_instr (bi_assign x e)) (at level 75).
Notation "x '<$-' 'lap(' w ',' e ')'" := (i_base_instr (bi_laplace x w e)) (at level 75).
Notation "c1 ';;' c2" := (i_seq c1 c2) (at level 75, right associativity).
