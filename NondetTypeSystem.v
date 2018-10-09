Require Export Cfuzzi.Pattern.
Require Export Cfuzzi.TypeSystem.

Definition M_nondet (A : Type) :=
  list (option A).

Definition M_nondet_return {A: Type} (a : A) : M_nondet A :=
  [Some a].

Search option.

Definition M_nondet_bind {A B: Type} (ma: M_nondet A) (f: A -> M_nondet B): M_nondet B :=
  List.fold_right
    (fun xs ys => xs ++ ys)
    []
    (List.map (fun oa => match oa with
                      | Some a => f a
                      | None => []
                      end) ma).

Notation "x '<--' ma ';;;' b" := (M_nondet_bind ma (fun x => b))
                                   (at level 75, right associativity) : M_nondet_scope.

Bind Scope M_nondet_scope with M_nondet.
Delimit Scope M_nondet_scope with M_nondet.

Definition M_option_bind {A B: Type} (ma: option A) (f: A -> option B): option B :=
  match ma with
  | Some a => f a
  | None => None
  end.

Notation "x '<--' ma ';;;' b" := (M_option_bind ma (fun x => b))
                                 (at level 75, right associativity) : M_option_scope.

Bind Scope M_option_scope with option.
Delimit Scope M_option_scope with option.

Eval compute in (
                 a <-- [Some 1; Some 2; Some 3]%Z ;;;
                   b <-- [Some 5; Some 6; Some 7]%Z ;;;
                   M_nondet_return (a, b)
               )%M_nondet.

Module NondetTS
       (E: Embedding)
       (Lap : Laplace E)
       (LOGIC: APRHL E Lap).

Module TSImpl := TS E Lap LOGIC.
Import TSImpl APRHLImpl SEMImpl LAPImpl CARImpl RP PP MP UP EImpl.

(* A typing rule is a pattern to match against, and a function that goes from
   the matched components, a typing environment to the output typing
   environment with potential failure.
 *)
Definition typing_rule_func := uni_env -> env -> option env.
Definition typing_rule := (cmd_pat * typing_rule_func)%type.

(* Step returns the resulting typing environment in a non-deterministic monad *)
Fixpoint step (rules: list typing_rule) (prog: cmd)
  : uni_env -> env -> M_nondet (env * option cmd)%type :=
  fun uenv senv =>
  match rules with
  | [] => []
  | ((cpat, f) :: rules) =>
    match match_cmd_prefix cpat prog uenv with
    | inl _ => []
    | inr (uenv', rem) =>
      match f uenv' senv with
      | Some env' => [Some (env', rem)]
      | None => []
      end
    end ++ (step rules prog uenv senv)
  end.

(* Non-deterministically search for all typing trees up to the given depth *)
Fixpoint search (rules: list typing_rule) (prog: cmd) (depth: nat)
  : uni_env -> env -> M_nondet (env * option cmd)%type :=
  fun uenv senv =>
  match depth with
  | O => []
  | S n' =>
    (
      uenv_senv_rem <-- step rules prog uenv senv ;;;
      match uenv_senv_rem with
      | (senv', None) => M_nondet_return (senv', None)
      (* Use the original unification environment so we can re-use unification
         variables across typing rules
       *)
      | (senv', Some rem) => search rules rem n' uenv senv'
      end
    )%M_nondet
  end.

Local Open Scope string_scope.

Definition assign_pat :=
  ("?x" <- "?e")%pat.
Definition assign_func : typing_rule_func :=
  fun uenv senv =>
    (x_ur <-- VariableDefinitions.VarMap.find "?x" uenv ;;;
     v <-- try_get_variable x_ur ;;;
     e_ur <-- VariableDefinitions.VarMap.find "?e" uenv ;;;
     rhs <-- try_get_expr e_ur ;;;
     let srhs := sens_expr senv rhs in
     Some (env_update v senv srhs)
    )%option.

Definition assign_rule := (assign_pat, assign_func).

Module TestAssign.

Definition assn_prog :=
  ("x" <- "x" :* 2%Z)%cmd.

Search env.

Eval compute in
    search [assign_rule] assn_prog 100 empty_uni_env (env_from_list [("x", 1%Z)]%list).
End TestAssign.

End NondetTS.