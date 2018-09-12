Require Import Coq.Strings.String.
Require Import ZArith.

Inductive tau :=
| t_int
| t_bool.

Definition var (t : tau) := string.

Inductive expr : tau -> Type :=
| e_lit : Z -> expr t_int
| e_var : forall {t}, var t -> expr t
| e_add : expr t_int -> expr t_int -> expr t_int
| e_minus : expr t_int -> expr t_int -> expr t_int
| e_mult : expr t_int -> expr t_int -> expr t_int
| e_div : expr t_int -> expr t_int -> expr t_int
| e_lt : expr t_int -> expr t_int -> expr t_bool
| e_eq : forall {t}, expr t -> expr t -> expr t_bool
| e_and : expr t_bool -> expr t_bool -> expr t_bool
| e_or : expr t_bool -> expr t_bool -> expr t_bool.

Coercion e_var : var >-> expr.
Coercion e_lit : Z >-> expr.
Check (1%Z : expr t_int).

Inductive base_instr :=
| bi_assign : forall {t}, var t -> expr t -> base_instr
| bi_laplace : var t_int
               -> Z (* width *)
               -> expr t_int (* center *)
               -> base_instr.

Reserved Notation "'cmd'".
Inductive instr :=
| i_base_instr : base_instr -> instr
| i_cond : expr t_bool -> cmd -> cmd -> instr
| i_while : expr t_bool -> cmd -> instr
where "'cmd'" := (list instr).

Notation "[ x ; .. ; y ]" :=
  (@cons instr x .. (@cons instr y (@nil instr)) ..).
Notation "'If' e 'then' c1 'else' c2 'end'" := (i_cond e c1 c2) (at level 65).
Notation "'If' e 'then_' c 'end'" := (i_cond e c nil) (at level 65).
Notation "'While' e 'do' c 'end'" := (i_while e c) (at level 65).
Notation "x '<-' e" := (i_base_instr (bi_assign x e)) (at level 65).
Notation "x '<$-' 'lap(' w ',' e ')'" := (i_base_instr (bi_laplace x w e)) (at level 65).

Example x : (var t_int):= "x"%string.
Check (x <$- lap(1, 2%Z)).
Check (x <- 2%Z).
Check (If (e_eq x x) then [ x <$- lap(1, 2%Z) ] else [x <- 2%Z] end).
Check (While (e_lt x 1%Z) do [ x <- (e_add x 1%Z) ] end).