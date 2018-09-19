Require Export Syntax.

Reserved Notation "'cmd_ext' ts" (at level 65, no associativity).
Inductive instr_ext : list tau -> Type :=
| i_bagmap : forall {ts}, (* TODO: make this a proper bag map *)
    instr ts -> instr_ext ts
| i_plain : forall {ts},
    instr ts -> instr_ext ts
where "'cmd_ext' ts" := (list (instr_ext ts)).

Coercion i_plain : instr >-> instr_ext.

Module Test.
  Definition ts := cons t_int (cons t_bool nil).
  Parameter x : var t_int ts.
  Check (x <- (e_lit 1%Z) : instr_ext ts).
End Test.

Fixpoint desugar_instr_ext {ts} (i : instr_ext ts) : instr ts :=
  match i with
  | i_bagmap i' => i'
  | i_plain i' => i'
  end.

Definition desugar_cmd_ext {ts} (c : cmd_ext ts) : cmd ts :=
  List.map desugar_instr_ext c.