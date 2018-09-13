Require Export Coq.Strings.String.
Require Export ZArith.

Inductive tau :=
| t_int
| t_bool.

Inductive val :=
| v_int : Z -> val
| v_bool : bool -> val.

Coercion v_int : Z >-> val.
Coercion v_bool : bool >-> val.

Definition var := string.

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
| e_or : expr -> expr -> expr.

Coercion e_var : var >-> expr.
Coercion e_lit : Z >-> expr.
Check (1%Z : expr).

Inductive base_instr :=
| bi_assign : var -> expr -> base_instr
| bi_laplace : var
               -> Z (* width *)
               -> expr (* center *)
               -> base_instr.

Reserved Notation "'cmd'".
Inductive instr :=
| i_base_instr : base_instr -> instr
| i_cond : expr -> cmd -> cmd -> instr
| i_while : expr -> cmd -> instr
where "'cmd'" := (list instr).

Notation "[ x ; .. ; y ]" :=
  (@cons instr x .. (@cons instr y (@nil instr)) ..).
Notation "'If' e 'then' c1 'else' c2 'end'" := (i_cond e c1 c2) (at level 65).
Notation "'If' e 'then_' c 'end'" := (i_cond e c nil) (at level 65).
Notation "'While' e 'do' c 'end'" := (i_while e c) (at level 65).
Notation "x '<-' e" := (i_base_instr (bi_assign x e)) (at level 65).
Notation "x '<$-' 'lap(' w ',' e ')'" := (i_base_instr (bi_laplace x w e)) (at level 65).

Example x : var := "x"%string.
Check (x <$- lap(1, 2%Z)).
Check (x <- 2%Z).
Check (If (e_eq x x) then [ x <$- lap(1, 2%Z) ] else [x <- 2%Z] end).
Check (While (e_lt x 1%Z) do [ x <- (e_add x 1%Z) ] end).