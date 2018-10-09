Require Export Cfuzzi.Pattern.
Require Export Cfuzzi.TypeSystem.

Definition M_nondet (A : Type) :=
  list A.

Definition M_nondet_return {A: Type} (a : A) : M_nondet A :=
  [a].

Definition M_nondet_bind {A B: Type} (ma: M_nondet A) (f: A -> M_nondet B): M_nondet B :=
  List.concat (List.map f ma).

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
                 a <-- [ 1;  2;  3]%Z ;;;
                   b <-- [ 5;  6;  7]%Z ;;;
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
Definition typing_rule_func := uni_env -> env -> option (M_nondet env).
Definition typing_rule := (cmd_pat * typing_rule_func)%type.

(* Step returns the resulting typing environment in a non-deterministic monad *)
Fixpoint step (rules: list typing_rule) (prog: cmd)
  : uni_env -> env -> M_nondet (env * (option cmd))%type :=
  fun uenv senv =>
  match rules with
  | [] => []
  | ((cpat, f) :: rules) =>
    match match_cmd_prefix cpat prog uenv with
    | inl _ => []
    | inr (uenv', rem) =>
      match f uenv' senv with
      | None => []
      | Some many_env' =>
        (env' <-- many_env' ;;;
         M_nondet_return (env', rem))%M_nondet
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
     Some [env_update v senv srhs]
    )%option.
Definition assign_rule := (assign_pat, assign_func).

Definition skip_pat :=
  (cpat_skip)%pat.
Definition skip_func : typing_rule_func :=
  fun uenv senv =>
    Some [senv].
Definition skip_rule := (skip_pat, skip_func).

Definition cond_sens_pat :=
  (If "?e"
   then "?c1"
   else "?c2"
   end)%pat.
Definition cond_sens_func : typing_rule_func :=
  (fun uenv senv =>
    e_ur <-- VariableDefinitions.VarMap.find "?e" uenv ;;;
    e <-- try_get_expr e_ur ;;;
    c1_ur <-- VariableDefinitions.VarMap.find "?c1" uenv ;;;
    c1 <-- try_get_cmd c1_ur ;;;
    c2_ur <-- VariableDefinitions.VarMap.find "?c2" uenv ;;;
    c2 <-- try_get_cmd c2_ur ;;;
    let modified_vars := (mvs c1 ++ mvs c2)%list in
    match sens_expr senv e with
    | Some s_e =>
      if (s_e >? 0)%Z
      then Some [List.fold_right (fun x senv => env_update x senv None) senv modified_vars]
      else None
    | None =>
      Some [List.fold_right (fun x senv => env_update x senv None) senv modified_vars]
    end)%option.
Definition cond_sens_rule := (cond_sens_pat, cond_sens_func).

Definition while_sens_pat :=
  (While "?e" do
         "?c"
   end)%pat.
Definition while_sens_func : typing_rule_func :=
  (fun uenv senv =>
     e_ur <-- VariableDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     c_ur <-- VariableDefinitions.VarMap.find "?c" uenv ;;;
     c <-- try_get_cmd c_ur ;;;
     let modified_vars := mvs c in
     match sens_expr senv e with
     | Some s_e =>
       if (s_e >? 0)%Z
       then Some [List.fold_right (fun x senv => env_update x senv None) senv modified_vars]
       else None
     | None
       => Some [List.fold_right (fun x senv => env_update x senv None) senv modified_vars]
     end
  )%option.
Definition while_sens_rule := (while_sens_pat, while_sens_func).

Definition if_nonsens_pat :=
  (If "?e"
   then "?c1"
   else "?c2"
   end)%pat.
Definition if_nonsens_func
           (recur: env -> cmd -> option (M_nondet env)): typing_rule_func :=
  fun uenv senv =>
    (e_ur <-- VariableDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     c1_ur <-- VariableDefinitions.VarMap.find "?c1" uenv ;;;
     c1 <-- try_get_cmd c1_ur ;;;
     c2_ur <-- VariableDefinitions.VarMap.find "?c2" uenv ;;;
     c2 <-- try_get_cmd c2_ur ;;;
     many_senv1 <-- recur senv c1 ;;;
     many_senv2 <-- recur senv c2 ;;;
     Some (
       senv1 <-- many_senv1 ;;;
       senv2 <-- many_senv2 ;;;
       M_nondet_return (env_max senv1 senv2)
     )%M_nondet
    )%option.
Definition if_nonsens_rule (recur: env -> cmd -> option (M_nondet env)) :=
  (if_nonsens_pat, if_nonsens_func recur).

Definition is_None (o : option cmd) :=
  match o with
  | None => true
  | _ => false
  end.

(* Filters the type checking results to the list that doesn't have any program
   fragments left *)
Definition get_complete_results (m : M_nondet (env * option cmd)) : M_nondet env :=
  List.map fst (List.filter (fun e_oc => is_None (snd e_oc)) m).

Definition lift_checker
           (m : env
                -> cmd
                -> M_nondet (env * option cmd))
  : env -> cmd -> option (M_nondet env) :=
  fun senv prog =>
  Some (get_complete_results (m senv prog)).

Fixpoint checker
         (fuel: nat)
         (senv: env)
         (prog: cmd) :=
  match fuel with
  | O => []
  | S n' =>
    let rule_set := [assign_rule;
                       skip_rule;
                       cond_sens_rule;
                       while_sens_rule;
                       if_nonsens_rule (lift_checker (checker n'))]
    in search rule_set prog fuel empty_uni_env senv
  end.

Module Tests.
Definition assn_prog (x : var) :=
  (x <- x :* 2%Z)%cmd.
Definition assn_prog2 :=
  (assn_prog "x";; assn_prog "x";; i_skip)%cmd.
Definition cond_prog :=
  (If 0%Z :< "x"
   then (assn_prog "x" ;; assn_prog "y" ;; assn_prog "y")
   else assn_prog "y"
   end)%cmd.

Eval compute in
    search [assign_rule]
           (assn_prog "x")
           1
           empty_uni_env
           (env_from_list [("x", 1%Z)]%list).
Eval compute in
    search [assign_rule; skip_rule]
           assn_prog2
           100
           empty_uni_env
           (env_from_list [("x", 1%Z)]%list).
Eval compute in
    search [assign_rule; skip_rule; cond_sens_rule]
           cond_prog
           100
           empty_uni_env
           (env_from_list [("x", 1%Z); ("y", 1%Z)]%list).
Eval compute in
    checker 100
            (env_from_list [("x", 0%Z); ("y", 1%Z)]%list)
            cond_prog.
End Tests.

End NondetTS.