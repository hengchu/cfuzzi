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
   the matched components, a typing environment to the output typing environment
   with potential failure. Since we don't allow strong updates, the simple types
   will not change, and the typing functions don't need to return them *)
Definition typing_rule_func := uni_env -> env -> st_env -> option (M_nondet env).
Definition typing_rule := (cmd_pat * typing_rule_func)%type.

(* Step returns the resulting typing environment in a non-deterministic monad *)
Fixpoint step (rules: list typing_rule) (prog: cmd)
  : uni_env -> env -> st_env  -> M_nondet (env * (option cmd))%type :=
  fun uenv senv stenv =>
  match rules with
  | [] => []
  | ((cpat, f) :: rules) =>
    match match_cmd_prefix cpat prog uenv with
    | inl _ => []
    | inr (uenv', rem) =>
      match f uenv' senv stenv with
      | None => []
      | Some many_env' =>
        (env' <-- many_env' ;;;
         M_nondet_return (env', rem))%M_nondet
      end
    end ++ (step rules prog uenv senv stenv)
  end.

(* Non-deterministically search for all typing trees up to the given depth *)
Fixpoint search (rules: list typing_rule) (prog: cmd) (depth: nat)
  : uni_env -> env -> st_env -> M_nondet (env * option cmd)%type :=
  fun uenv senv stenv =>
  match depth with
  | O => []
  | S n' =>
    (
      uenv_senv_rem <-- step rules prog uenv senv stenv ;;;
      match uenv_senv_rem with
      | (senv', None) => M_nondet_return (senv', None)
      (* Use the original unification environment so we can re-use unification
         variables across typing rules
       *)
      | (senv', Some rem) => search rules rem n' uenv senv' stenv
      end
    )%M_nondet
  end.

Definition if_sensitive {A: Type} (senv: env) (tenv: st_env) (e: expr) (k : option A) : option A :=
  match sens_expr senv tenv e with
  | None => k
  | Some s => if (s >? 0)%Z then k else None
  end.

Local Open Scope string_scope.

Definition assign_pat :=
  ("?x" <- "?e")%pat.
Definition assign_func : typing_rule_func :=
  fun uenv senv stenv =>
    (x_ur <-- BaseDefinitions.VarMap.find "?x" uenv ;;;
     v <-- try_get_variable x_ur ;;;
     e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     rhs <-- try_get_expr e_ur ;;;
     let srhs := sens_expr senv stenv rhs in
     Some [env_update v senv srhs]
    )%option.
Definition assign_rule := (assign_pat, assign_func).

Definition skip_pat :=
  (cpat_skip)%pat.
Definition skip_func : typing_rule_func :=
  fun uenv senv stenv =>
    Some [senv].
Definition skip_rule := (skip_pat, skip_func).

Definition cond_sens_pat :=
  (If "?e"
   then "?c1"
   else "?c2"
   end)%pat.
Definition cond_sens_func : typing_rule_func :=
  (fun uenv senv stenv =>
    e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
    e <-- try_get_expr e_ur ;;;
    c1_ur <-- BaseDefinitions.VarMap.find "?c1" uenv ;;;
    c1 <-- try_get_cmd c1_ur ;;;
    c2_ur <-- BaseDefinitions.VarMap.find "?c2" uenv ;;;
    c2 <-- try_get_cmd c2_ur ;;;
    let modified_vars := (mvs c1 ++ mvs c2)%list in
    if_sensitive
      senv stenv e
      (Some [List.fold_right (fun x senv => env_update x senv None) senv modified_vars]%list)
  )%option.
Definition cond_sens_rule := (cond_sens_pat, cond_sens_func).

Definition while_sens_pat :=
  (While "?e" do
         "?c"
   end)%pat.
Definition while_sens_func : typing_rule_func :=
  (fun uenv senv stenv =>
     e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     c_ur <-- BaseDefinitions.VarMap.find "?c" uenv ;;;
     c <-- try_get_cmd c_ur ;;;
     let modified_vars := mvs c in
     if_sensitive
       senv stenv e
       (Some [List.fold_right (fun x senv => env_update x senv None) senv modified_vars]%list)
  )%option.
Definition while_sens_rule := (while_sens_pat, while_sens_func).

Definition if_nonsens_pat :=
  (If "?e"
   then "?c1"
   else "?c2"
   end)%pat.
Definition if_nonsens_func
           (recur: env -> st_env -> cmd -> option (M_nondet env)): typing_rule_func :=
  fun uenv senv stenv =>
    (e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     s_e <-- sens_expr senv stenv e ;;;
     if (s_e >? 0)%Z
     then None
     else
       c1_ur <-- BaseDefinitions.VarMap.find "?c1" uenv ;;;
       c1 <-- try_get_cmd c1_ur ;;;
       c2_ur <-- BaseDefinitions.VarMap.find "?c2" uenv ;;;
       c2 <-- try_get_cmd c2_ur ;;;
       many_senv1 <-- recur senv stenv c1 ;;;
       many_senv2 <-- recur senv stenv c2 ;;;
       Some (
         senv1 <-- many_senv1 ;;;
         senv2 <-- many_senv2 ;;;
         M_nondet_return (env_max senv1 senv2)
       )%M_nondet
    )%option.
Definition if_nonsens_rule (recur: env -> st_env -> cmd -> option (M_nondet env)) :=
  (if_nonsens_pat, if_nonsens_func recur).

Definition while_nonsens_pat :=
  (While "?e" do
         "?c"
   end)%pat.
Definition while_nonsens_func (recur: env -> cmd -> option (M_nondet env)): typing_rule_func :=
  fun uenv senv stenv =>
    (e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
     e <-- try_get_expr e_ur ;;;
     s_e <-- sens_expr senv stenv e ;;;
     if (s_e >? 0)%Z
     then None
     else c_ur <-- BaseDefinitions.VarMap.find "?c" uenv ;;;
        c <-- try_get_cmd c_ur ;;;
        many_senv' <-- recur senv c ;;;
        Some (
          senv' <-- many_senv' ;;;
          if BaseDefinitions.VarMap.equal Z.eqb senv senv'
          then M_nondet_return senv'
          else []
        )%M_nondet
    )%option.

Definition cond_inc_pat :=
  (If "?e"
   then "?x" <- epv "?x" :+ epl "?k1"
   else "?x" <- epv "?x" :+ epl "?k2"
   end)%pat.
Definition cond_inc_func : typing_rule_func :=
  fun uenv senv stenv =>
    (
      e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
      e <-- try_get_expr e_ur ;;;
      if_sensitive senv stenv e
        (x_ur <-- BaseDefinitions.VarMap.find "?x" uenv ;;;
         x <-- try_get_variable x_ur ;;;
         k1_ur <-- BaseDefinitions.VarMap.find "?k1" uenv ;;;
         k1 <-- try_get_Z k1_ur ;;;
         k2_ur <-- BaseDefinitions.VarMap.find "?k2" uenv ;;;
         k2 <-- try_get_Z k2_ur ;;;
         let diff := Z.abs (k1 - k2)%Z in
         match BaseDefinitions.VarMap.find x senv with
         | None => Some [senv]
         | Some s => Some [env_update x senv (Some (s + diff)%Z)]
         end)%option
    )%option.
Definition cond_inc_rule := (cond_inc_pat, cond_inc_func).

Definition simple_arr_map_pat :=
  ("?idx" <- 0%Z ;;
   len("?arr_out") <- len(epv "?arr_in") ;;
   While (epv "?idx") :< len(epv "?arr_in") do
     "?t" <- (epv "?arr_in") !! (epv "?idx") ;;
     at("?arr_out", epv "?idx") <- "?e" ;;
     "?idx" <- epv "?idx" :+ epl 1%Z
   end)%pat.

Definition simple_arr_map_func: typing_rule_func :=
  fun uenv senv stenv =>
    (idx_ur <-- BaseDefinitions.VarMap.find "?idx" uenv ;;;
     idx <-- try_get_variable idx_ur ;;;
     s_idx <-- BaseDefinitions.VarMap.find idx senv ;;;
     if (s_idx >? 0)%Z
     then None
     else (
         t_ur <-- BaseDefinitions.VarMap.find "?t" uenv ;;;
         t <-- try_get_variable t_ur ;;;
         e_ur <-- BaseDefinitions.VarMap.find "?e" uenv ;;;
         e <-- try_get_expr e_ur ;;;
         match List.remove var_eqdec t (fvs e) with
         | _ :: _ => None
         | [] => (
             arr_in_ur <-- BaseDefinitions.VarMap.find "?arr_in" uenv ;;;
             arr_in <-- try_get_variable arr_in_ur ;;;
             arr_out_ur <-- BaseDefinitions.VarMap.find "?arr_out" uenv ;;;
             arr_out <-- try_get_variable arr_out_ur ;;;
             let senv' := env_update t senv (BaseDefinitions.VarMap.find arr_in senv) in
             let s_e := sens_expr senv' stenv e in
             Some [env_update arr_out senv' s_e]
           )%option
         end
       )%option
    )%option.
Definition simple_arr_map_rule := (simple_arr_map_pat, simple_arr_map_func).

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
                -> st_env
                -> cmd
                -> M_nondet (env * option cmd))
  : env -> st_env -> cmd -> option (M_nondet env) :=
  fun senv stenv prog =>
  Some (get_complete_results (m senv stenv prog)).

Fixpoint checker
         (fuel: nat)
         (senv: env)
         (stenv: st_env)
         (prog: cmd) :=
  match fuel with
  | O => []
  | S n' =>
    let rule_set := [assign_rule;
                       skip_rule;
                       cond_sens_rule;
                       while_sens_rule;
                       if_nonsens_rule (lift_checker (checker n'));
                       cond_inc_rule;
                       simple_arr_map_rule
                    ]
    in search rule_set prog fuel empty_uni_env senv stenv
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

Definition cond_inc_prog :=
  (If 0%Z :< "x"
   then "x" <- "x" :+ 5%Z
   else "x" <- "x" :+ 10%Z
   end)%cmd.

Definition arr_map_prog :=
  (
    "i" <- 0%Z ;;
    len("out") <- len("in") ;;
    While ("i" :< len("in"))%expr do
      "t" <- ("in" !! "i")%expr ;;
      at("out", "i") <- ("t" :* 10%Z)%expr ;;
      "i" <- ("i" :+ 1%Z)%expr
    end
  )%cmd.

Eval compute in env_max
                  (env_from_list [("x", 2%Z)]%list)
                  (env_from_list [("x", 1%Z); ("y", 10%Z)]%list).

Eval compute in env_max
                  (env_from_list [("x", 1%Z); ("y", 10%Z)]%list)
                  (env_from_list [("x", 2%Z)]%list).

Eval compute in
    search [assign_rule]
           (assn_prog "x")
           1
           empty_uni_env
           (env_from_list [("x", 1%Z)]%list)
           (varmap_from_list [("x", t_int)]%list).
Eval compute in
    search [assign_rule; skip_rule]
           assn_prog2
           100
           empty_uni_env
           (env_from_list [("x", 1%Z)]%list)
           (varmap_from_list [("x", t_int)]%list).
Eval compute in
    search [assign_rule; skip_rule; cond_sens_rule]
           cond_prog
           100
           empty_uni_env
           (env_from_list [("x", 1%Z); ("y", 1%Z)]%list)
           (varmap_from_list [("x", t_int); ("y", t_int)]%list).
Eval compute in
    checker 100
            (env_from_list [("x", 0%Z); ("y", 1%Z)]%list)
            (varmap_from_list [("x", t_int); ("y", t_int)]%list)
            cond_prog.
Eval compute in
    checker 100
            (env_from_list [("x", 1%Z); ("y", 1%Z)]%list)
            (varmap_from_list [("x", t_int); ("y", t_int)]%list)
            cond_prog.
Eval compute in
    checker 100
            (env_from_list [("x", 1%Z)]%list)
            (varmap_from_list [("x", t_int)]%list)
            cond_inc_prog.
Eval compute in
    checker 100
            (env_from_list [("i", 0%Z); ("in", 1%Z); ("out", 0%Z); ("t", 0%Z)]%list)
            (varmap_from_list [("i", t_int); ("in", t_arr t_int); ("out", t_arr t_int); ("t", t_int)]%list)
            arr_map_prog.
End Tests.

End NondetTS.
