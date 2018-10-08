Require Export Syntax.

Definition uni_var := string.

Inductive uni_res :=
| uni_variable : var -> uni_res
| uni_Z : Z -> uni_res
| uni_positive : positive -> uni_res
| uni_expr : expr -> uni_res
| uni_base_instr : base_instr -> uni_res
| uni_cmd : cmd -> uni_res.

Lemma uni_res_eqdec : forall ur1 ur2 : uni_res,
    {ur1 = ur2} + {ur1 <> ur2}.
Proof.
  destruct ur1.
  - intros ur2; destruct ur2; prune_eqdec_cases.
    destruct (var_eqdec v v0).
    + subst; auto.
    + right; intros contra; inversion contra; apply n; auto.
  - intros ur2; destruct ur2; prune_eqdec_cases.
    destruct (Z.eq_dec z z0).
    + subst; auto.
    + right; intros contra; inversion contra; apply n; auto.
  - intros ur2; destruct ur2; prune_eqdec_cases.
    destruct (Pos.eq_dec p p0).
    + subst; auto.
    + right; intros contra; inversion contra; apply n; auto.
  - intros ur2; destruct ur2; prune_eqdec_cases.
    destruct (expr_eqdec e e0).
    + subst; auto.
    + right; intros contra; inversion contra; apply n; auto.
  - intros ur2; destruct ur2; prune_eqdec_cases.
    destruct (base_instr_eqdec b b0).
    + subst; auto.
    + right; intros contra; inversion contra; apply n; auto.
  - intros ur2; destruct ur2; prune_eqdec_cases.
    destruct (cmd_eqdec c c0).
    + subst; auto.
    + right; intros contra; inversion contra; apply n; auto.
Defined.

Inductive atom_pat (T : Type) :=
| apat_atom : T -> atom_pat T
| apat_uni : uni_var -> atom_pat T.

Definition var_pat := atom_pat var.
Definition Z_pat := atom_pat Z.
Definition positive_pat := atom_pat positive.

Definition uni_env := VarMap.t uni_res.

(* Produces either a list of disagreeing unification variables, or a union of
   the two environments *)
Definition uni_env_union' (e1 e2 : uni_env) : ((list uni_var) * uni_env) :=
  VarMap.fold (fun uv ur acc =>
                 match acc with
                 | (bad_uvs, union) =>
                   match VarMap.find uv union with
                   | None => (bad_uvs, VarMap.add uv ur union)
                   | Some ur2 => if uni_res_eqdec ur ur2
                                then acc
                                else (uv :: bad_uvs, union)
                   end
                 end)
              e1
              (@nil uni_var, e2).

Definition M_uni := sum (list uni_var).
Definition M_uni_return {T} (r : T) : M_uni T := inr r.
Definition M_uni_bind {A B} (ma : M_uni A) (f : A -> M_uni B) : M_uni B :=
  match ma with
  | inl err => inl err
  | inr a => f a
  end.

Notation "a '<--' ma ';;;' p" := (M_uni_bind ma (fun a => p))
                                 (at level 75, right associativity) : M_uni_scope.
Bind Scope M_uni_scope with M_uni.
Delimit Scope M_uni_scope with M_uni.

Definition uni_env_union (e1 e2 : uni_env) : M_uni uni_env :=
  match uni_env_union' e1 e2 with
  | (nil, union) => inr union
  | (bad_uvs, _) => inl bad_uvs
  end.

Module TestUnion.
  Definition build_uni_env_from_list (urs : list (uni_var * uni_res)) : uni_env :=
    List.fold_right (fun uvur e =>
                       VarMap.add (fst uvur) (snd uvur) e)
                    (@VarMap.empty uni_res)
                    urs.

  Definition e1 := build_uni_env_from_list
                     [("x"%string, uni_Z 1%Z);
                        ("y"%string, uni_variable "k"%string)].

  Definition e2 := build_uni_env_from_list
                     [("x"%string, uni_Z 1%Z)].

  Definition e3 := build_uni_env_from_list
                     [("x"%string, uni_Z 2%Z);
                        ("y"%string, uni_variable "k"%string)].

  Eval compute in uni_env_union e1 e2.
  Eval compute in uni_env_union e1 e3.

  Definition test_val :=
    (e1' <-- M_uni_return e1 ;;;
     e2' <-- M_uni_return e2 ;;;
     M_uni_return (e1', e2'))%M_uni.

  Eval compute in test_val.

End TestUnion.

Inductive expr_pat :=
| epat_wildcard : uni_var -> expr_pat
| epat_lit : Z_pat -> expr_pat
| epat_var : var_pat -> expr_pat
| epat_add : expr_pat -> expr_pat -> expr_pat
| epat_minus : expr_pat -> expr_pat -> expr_pat
| epat_mult : expr_pat -> expr_pat -> expr_pat
| epat_div : expr_pat -> expr_pat -> expr_pat
| epat_lt : expr_pat -> expr_pat -> expr_pat
| epat_eq : expr_pat -> expr_pat -> expr_pat
| epat_and : expr_pat -> expr_pat -> expr_pat
| epat_or : expr_pat -> expr_pat -> expr_pat
| epat_index : expr_pat -> expr_pat -> expr_pat
| epat_length : expr_pat -> expr_pat.

Definition epv : var_pat -> expr_pat := epat_var.
Definition epl : Z_pat -> expr_pat := epat_lit.

Definition match_var (vp : var_pat) (v : var) : uni_env -> M_uni uni_env :=
  fun env =>
  match vp with
  | apat_atom _ v' => if var_eqdec v v'
                   then M_uni_return env
                   else inl []
  | apat_uni _ uv => M_uni_return (VarMap.add uv (uni_variable v) env)
  end.

Definition match_pos (pp : positive_pat) (p : positive) : uni_env -> M_uni uni_env :=
  fun env =>
    match pp with
    | apat_atom _ p' => if Pos.eq_dec p p'
                        then M_uni_return env
                        else inl []
    | apat_uni _ uv => M_uni_return (VarMap.add uv (uni_positive p) env)
    end.

Definition match_Z (zp : Z_pat) (z : Z) : uni_env -> M_uni uni_env :=
  fun env =>
    match zp with
    | apat_atom _ z' => if Z.eq_dec z z'
                       then M_uni_return env
                       else inl []
    | apat_uni _ uv => M_uni_return (VarMap.add uv (uni_Z z) env)
    end.

Fixpoint match_expr (ep : expr_pat) (e : expr) : uni_env -> M_uni uni_env :=
  fun env =>
    match ep, e with
    | epat_wildcard x, _ => M_uni_return (VarMap.add x (uni_expr e) env)
    | epat_lit zp, e_lit z =>
      match_Z zp z env
    | epat_var vp, e_var v => (
        env' <-- match_var vp v env ;;;
        M_uni_return env'
      )%M_uni
    | epat_add ep1 ep2, e_add e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_minus ep1 ep2, e_minus e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_mult ep1 ep2, e_mult e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_div ep1 ep2, e_div e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_lt ep1 ep2, e_lt e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_eq ep1 ep2, e_eq e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_and ep1 ep2, e_and e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_or ep1 ep2, e_or e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_index ep1 ep2, e_index e1 e2 => (
        env1 <-- match_expr ep1 e1 env ;;;
        env2 <-- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_length ep1, e_length e1 =>
        match_expr ep1 e1 env
    | _, _ => inl []
    end.

Inductive bi_pat :=
| bipat_wildcard : uni_var -> bi_pat
| bipat_laplace : var_pat -> positive_pat -> expr_pat -> bi_pat
| bipat_assign : var_pat -> expr_pat -> bi_pat
| bipat_index_assign : var_pat -> expr_pat -> expr_pat -> bi_pat
| bipat_length_assign : var_pat -> expr_pat -> bi_pat.

Fixpoint match_bi (bp : bi_pat) (bi : base_instr) : uni_env -> M_uni uni_env :=
  match bp, bi with
  | bipat_wildcard x, _ =>
    fun env => M_uni_return (VarMap.add x (uni_base_instr bi) env)
  | bipat_laplace vp pp ep, bi_laplace v p e =>
    fun env =>
      (env1 <-- match_var vp v env ;;;
       env2 <-- match_pos pp p env ;;;
       env3 <-- match_expr ep e env ;;;
       env12 <-- uni_env_union env1 env2 ;;;
       uni_env_union env12 env3)%M_uni
  | bipat_assign vp ep,
    bi_assign v e =>
    fun env => (
        env1 <-- match_var vp v env ;;;
        env2 <-- match_expr ep e env ;;;
        uni_env_union env1 env2
      )%M_uni
  | bipat_index_assign vp ep1 ep2,
    bi_index_assign v e1 e2 =>
    fun env => (
        env1 <-- match_var vp v env ;;;
        env2 <-- match_expr ep1 e1 env ;;;
        env3 <-- match_expr ep2 e2 env ;;;
        env12 <-- uni_env_union env1 env2 ;;;
        uni_env_union env12 env3
      )%M_uni
  | bipat_length_assign vp ep,
    bi_length_assign v e =>
    fun env => (
        env1 <-- match_var vp v env ;;;
        env2 <-- match_expr ep e env ;;;
        uni_env_union env1 env2
      )%M_uni
  | _, _ => fun _ => inl []
  end.

Inductive cmd_pat :=
| cpat_wildcard : uni_var -> cmd_pat
| cpat_skip : cmd_pat
| cpat_base_instr : bi_pat -> cmd_pat
| cpat_cond : expr_pat -> cmd_pat -> cmd_pat -> cmd_pat
| cpat_while : expr_pat -> cmd_pat -> cmd_pat
| cpat_seq : cmd_pat -> cmd_pat -> cmd_pat.

Fixpoint match_cmd (cp : cmd_pat) (c : cmd) : uni_env -> M_uni uni_env :=
  match cp, c with
  | cpat_wildcard x, _ => fun env => M_uni_return (VarMap.add x (uni_cmd c) env)
  | cpat_skip, i_skip => fun env => M_uni_return env
  | cpat_base_instr bp,
    i_base_instr bi =>
    fun env => match_bi bp bi env
  | cpat_cond ep cp1 cp2,
    i_cond e c1 c2 =>
    fun env => (
        env1 <-- match_expr ep e env ;;;
        env2 <-- match_cmd cp1 c1 env ;;;
        env3 <-- match_cmd cp2 c2 env ;;;
        env12 <-- uni_env_union env1 env2 ;;;
        uni_env_union env12 env3
      )%M_uni
  | cpat_while ep cp,
    i_while e c =>
    fun env => (
        env1 <-- match_expr ep e env ;;;
        env2 <-- match_cmd cp c env ;;;
        uni_env_union env1 env2
      )%M_uni
  | cpat_seq cp1 cp2,
    i_seq c1 c2 =>
    fun env => (
        env1 <-- match_cmd cp1 c1 env ;;;
        env2 <-- match_cmd cp2 c2 env ;;;
        uni_env_union env1 env2
      )%M_uni
  | _, _ => fun _ => inl []
  end.

(* Here are a bunch of things that make writing patterns a bit easier... *)
Definition ppat : positive -> positive_pat := apat_atom positive.
Definition zpat : Z -> Z_pat := apat_atom Z.
Definition vpat : var -> var_pat := apat_atom var.

Coercion ppat : positive >-> positive_pat.
Coercion zpat : Z >-> Z_pat.

Definition str_uni_var : string -> uni_var := fun x => x.
Definition ppat_wildcard : uni_var -> positive_pat := apat_uni positive.
Definition vpat_wildcard : uni_var -> var_pat := apat_uni var.

Coercion str_uni_var : string >-> uni_var.
Coercion epat_wildcard : uni_var >-> expr_pat.
Coercion bipat_wildcard : uni_var >-> bi_pat.
Coercion cpat_wildcard : uni_var >-> cmd_pat.
Coercion ppat_wildcard : uni_var >-> positive_pat.
Coercion vpat_wildcard : uni_var >-> var_pat.

Coercion epat_var : var_pat >-> expr_pat.
Coercion epat_lit : Z_pat >-> expr_pat.


Notation "e1 ':+' e2" := (epat_add e1 e2) (at level 65, left associativity) : pat_scope.
Notation "e1 ':-' e2" := (epat_minus e1 e2) (at level 65, left associativity) : pat_scope.
Notation "e1 ':*' e2" := (epat_mult e1 e2) (at level 64, left associativity) : pat_scope.
Notation "e1 ':/' e2" := (epat_div e1 e2) (at level 64, left associativity) : pat_scope.
Notation "e1 ':<' e2" := (epat_lt e1 e2) (at level 68, no associativity) : pat_scope.
Notation "e1 ':==' e2" := (epat_eq e1 e2) (at level 69, no associativity) : pat_scope.
Notation "e1 ':&&' e2" := (epat_and e1 e2) (at level 66, left associativity) : pat_scope.
Notation "e1 '!!' e2" := (epat_index e1 e2) (at level 63, no associativity) : pat_scope.
Notation "'len(' e ')'" := (epat_length e) (at level 63) : pat_scope.

Notation "'If' e 'then' c1 'else' c2 'end'" := (cpat_cond e c1 c2) (at level 75) : pat_scope.
Notation "'If' e 'then_' c 'end'" := (cpat_cond e c cpat_skip) (at level 75) : pat_scope.
Notation "'While' e 'do' c 'end'" := (cpat_while e c) (at level 75) : pat_scope.
Notation "'at(' x ','  e1 ')' '<-' e2" := (cpat_base_instr (bipat_index_assign x e1 e2)) (at level 75) : pat_scope.
Notation "'len(' x ')' '<-' e" := (cpat_base_instr (bipat_length_assign x e)) (at level 75) : pat_scope.
Notation "x '<-' e" := (cpat_base_instr (bipat_assign x e)) (at level 75) : pat_scope.
Notation "x '<$-' 'lap(' w ',' e ')'" := (cpat_base_instr (bipat_laplace x w e)) (at level 75) : pat_scope.
Notation "c1 ';;' c2" := (cpat_seq c1 c2) (at level 75, right associativity) : pat_scope.

Delimit Scope pat_scope with pat.

Print Coercion Paths string expr_pat.

Definition empty_uni_env := VarMap.empty uni_res.

Module TestNotation.
  Local Open Scope string_scope.
  Local Close Scope list_scope.
  Check (epat_add "?x" "?y").
  Check (epat_add (epat_var "x") "?y").

  Definition test_seq_pat := ("?c1" ;; "?c1" ;; "?c2")%pat.
  Eval compute in match_cmd test_seq_pat (i_skip ;; i_skip ;; i_skip ;; i_skip)%cmd (VarMap.empty uni_res).
  Eval compute in match_cmd cpat_skip i_skip (VarMap.empty uni_res).

  Definition test_assn_pat := ("?x" <- (epat_lit 1%Z) :+ "?rhs")%pat.
  Definition test_assn := ("x" <- (el 1%Z) :+ (el 2%Z))%cmd.
  Eval compute in match_cmd test_assn_pat test_assn (VarMap.empty uni_res).

  Eval compute in match_expr ((epat_lit 1%Z) :< "?bound")%pat (el 1%Z :< ev "y")%expr (VarMap.empty uni_res).

  Definition test_cond_pat := (If ((epat_lit 1%Z) :< "?bound") then_ test_assn_pat end)%pat.
  Definition test_cond := (If (el 1%Z) :< ev "y" then_ test_assn end)%cmd.
  Eval compute in match_cmd test_cond_pat test_cond (VarMap.empty uni_res).

  Check (len("?x") <- "?y")%pat.
  Eval compute in match_cmd (len("?x") <- "?y")%pat (len("x") <- "y" !! "i")%cmd empty_uni_env.

  (* WARNING: Notice the difference between these subtly different patterns *)
  Eval compute in match_cmd ("?x" <$- lap("?w", "?y"))%pat ("x" <$- lap(1%positive, "y")) empty_uni_env.
  Eval compute in match_cmd ("?x" <$- lap("?w", epv "?y"))%pat ("x" <$- lap(1%positive, "y")) empty_uni_env.
  Eval compute in match_cmd ("?x" <$- lap("?w", vpat "?y"))%pat ("x" <$- lap(1%positive, "y")) empty_uni_env.

  Check (at("?x", "?idx") <- "?y")%pat.
  Eval compute in match_cmd (at("?x", "?idx") <- "?y")%pat (at("x", ev "idx") <- "y")%cmd empty_uni_env.

  Definition complex_pat :=
    ("?idx" <- 0%Z ;;
     While (epv "?idx") :< len(epv "?x") do
       at("?x", epv "?idx") <- ((epv "?y") !! epv "?idx")%pat
     end
    )%pat.
  Definition complex_prog :=
    ("idx" <- 0%Z ;;
    While ("idx" :< len("x"))%expr do
      at("x", "idx") <- "y" !! "idx"
    end)%cmd.
  Eval compute in match_cmd complex_pat complex_prog empty_uni_env.

End TestNotation.

(* TODO: setup some kind of correctness lemma that says if we substitute the
   pattern with the resulting unification environment, then we get the matched
   syntax tree
*)
