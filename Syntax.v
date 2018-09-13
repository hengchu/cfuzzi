Require Export Coq.Strings.String.
Require Export ZArith.
Require Export Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Require Export VariableDefinitions.
Require Export VarMap.

Inductive tau :=
| t_int
| t_bool.

Inductive val :=
| v_int : Z -> val
| v_bool : bool -> val.

Coercion v_int : Z >-> val.
Coercion v_bool : bool >-> val.

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
Example y : var := "y"%string.
Check (x <$- lap(1, 2%Z)).
Check (x <- 2%Z).
Check (If (e_eq x x) then [ x <$- lap(1, 2%Z) ] else [x <- 2%Z] end).
Check (While (e_lt x 1%Z) do [ x <- (e_add x 1%Z) ] end).

Definition s_tau := (N * tau)%type.

Definition env := VarMap.t s_tau.
Definition empty : env := VarMap.empty s_tau.
Definition extend (v : var) (s : N) (t : tau) (g : env) :=
  VarMap.add v (s, t) g.

Inductive wf_env : env -> Prop :=
| wf_env_empty : wf_env empty
| wf_env_add : forall v st g, ~(VarMap.In v g) -> wf_env g -> wf_env (VarMap.add v st g).

Hint Constructors wf_env.

Notation "x ':_(' s ')' t ':+:' g" := (extend x s t g) (at level 65, right associativity).

Check (x :_(1) t_int :+: empty).
Check (x :_(0) t_bool :+: y :_(1) t_int :+: empty).

Eval compute in ( VarMap.mem x (empty) ).
Eval compute in ( VarMap.mem x (x :_(1) t_int :+: empty) ).

Example test1: wf_env (x :_(1) t_int :+: empty).
Proof.
  constructor.
  - intro contra.
    Search VarMap.In.
    apply VarMap.mem_1 in contra; vm_compute in contra; inversion contra.
  - constructor.
Qed.

Example test2: wf_env (x :_(1) t_int :+: y :_(1) t_bool :+: empty).
Proof.
  constructor.
  - intro contra.
    apply VarMap.mem_1 in contra; vm_compute in contra; inversion contra.
  - constructor.
    + intro contra.
      apply VarMap.mem_1 in contra; vm_compute in contra; inversion contra.
    + constructor.
Qed.