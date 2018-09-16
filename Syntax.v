Require Export Coq.Strings.String.
Require Export ZArith.
Require Export Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Export VariableDefinitions.

Inductive expr : tau -> list tau -> Type :=
| e_lit : forall {ts}, Z -> expr t_int ts
| e_var : forall {t : tau} {ts : list tau}, var t ts -> expr t ts
| e_add : forall {ts}, expr t_int ts -> expr t_int ts -> expr t_int ts
| e_minus : forall {ts}, expr t_int ts -> expr t_int ts -> expr t_int ts
| e_mult : forall {ts}, expr t_int ts -> expr t_int ts -> expr t_int ts
| e_div : forall {ts}, expr t_int ts -> expr t_int ts -> expr t_int ts
| e_lt : forall {ts}, expr t_int ts -> expr t_int ts -> expr t_bool ts
| e_eq : forall {ts}, expr t_int ts -> expr t_int ts -> expr t_bool ts
| e_and : forall {ts}, expr t_bool ts -> expr t_bool ts -> expr t_bool ts
| e_or : forall {ts}, expr t_bool ts -> expr t_bool ts -> expr t_bool ts.

Coercion e_lit : Z >-> expr.
Coercion e_var : var >-> expr.

Check ((e_lit 1%Z) : expr t_int (cons t_int nil)).

Inductive base_instr : list tau -> Type :=
| bi_assign : forall {t ts}, var t ts -> expr t ts -> base_instr ts
| bi_laplace : forall {ts c}, var t_int ts
               -> (c > 0)%Z (* width *)
               -> expr t_int ts (* center *)
               -> base_instr ts.

Reserved Notation "'cmd' ts" (at level 65, no associativity).
Inductive instr : list tau -> Type :=
| i_base_instr : forall {ts}, base_instr ts -> instr ts
| i_cond : forall {ts}, expr t_bool ts -> cmd ts -> cmd ts -> instr ts
| i_while : forall {ts}, expr t_bool ts -> cmd ts -> instr ts
where "'cmd' ts" := (list (instr ts)).

Notation "'If' e 'then' c1 'else' c2 'end'" := (i_cond e c1 c2) (at level 65).
Notation "'If' e 'then_' c 'end'" := (i_cond e c nil) (at level 65).
Notation "'While' e 'do' c 'end'" := (i_while e c) (at level 65).
Notation "x '<-' e" := (i_base_instr (bi_assign x e)) (at level 65).
Notation "x '<$-' 'lap(' w ',' e ')'" := (i_base_instr (bi_laplace x w e)) (at level 65).
