Require Import Cfuzzi.Syntax.

Definition uni_var := string.

Inductive uni_res :=
| uni_variable : var -> uni_res
| uni_Z : Z -> uni_res
| uni_positive : positive -> uni_res
| uni_expr : expr -> uni_res
| uni_base_instr : base_instr -> uni_res
| uni_cmd : cmd -> uni_res.

Definition try_get_variable : uni_res -> option var :=
  fun ur => match ur with
         | uni_variable v => Some v
         | _ => None
         end.

Definition try_get_Z : uni_res -> option Z :=
  fun ur => match ur with
         | uni_Z z => Some z
         | _ => None
         end.

Definition try_get_positive : uni_res -> option positive :=
  fun ur => match ur with
         | uni_positive p => Some p
         | _ => None
         end.

Definition try_get_expr : uni_res -> option expr :=
  fun ur => match ur with
         | uni_expr e => Some e
         | _ => None
         end.

Definition try_get_base_instr : uni_res -> option base_instr :=
  fun ur => match ur with
         | uni_base_instr bi => Some bi
         | _ => None
         end.

Definition try_get_cmd : uni_res -> option cmd :=
  fun ur => match ur with
         | uni_cmd c => Some c
         | _ => None
         end.

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

Definition uni_env := BaseDefinitions.VarMap.t uni_res.

(* Produces either a list of disagreeing unification variables, or a union of
   the two environments *)
Definition uni_env_union' (e1 e2 : uni_env) : ((list uni_var) * uni_env) :=
  BaseDefinitions.VarMap.fold (fun uv ur acc =>
                 match acc with
                 | (bad_uvs, union) =>
                   match BaseDefinitions.VarMap.find uv union with
                   | None => (bad_uvs, BaseDefinitions.VarMap.add uv ur union)
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
  fun env =>
  match bp, bi with
  | bipat_wildcard x, _ =>
    M_uni_return (VarMap.add x (uni_base_instr bi) env)
  | bipat_laplace vp pp ep, bi_laplace v p e =>
      (env1 <-- match_var vp v env ;;;
       env2 <-- match_pos pp p env ;;;
       env3 <-- match_expr ep e env ;;;
       env12 <-- uni_env_union env1 env2 ;;;
       uni_env_union env12 env3)%M_uni
  | bipat_assign vp ep,
    bi_assign v e =>
    (
        env1 <-- match_var vp v env ;;;
        env2 <-- match_expr ep e env ;;;
        uni_env_union env1 env2
      )%M_uni
  | bipat_index_assign vp ep1 ep2,
    bi_index_assign v e1 e2 =>
    (
        env1 <-- match_var vp v env ;;;
        env2 <-- match_expr ep1 e1 env ;;;
        env3 <-- match_expr ep2 e2 env ;;;
        env12 <-- uni_env_union env1 env2 ;;;
        uni_env_union env12 env3
      )%M_uni
  | bipat_length_assign vp ep,
    bi_length_assign v e =>
    (
        env1 <-- match_var vp v env ;;;
        env2 <-- match_expr ep e env ;;;
        uni_env_union env1 env2
      )%M_uni
  | _, _ => inl []
  end.

Inductive cmd_pat :=
| cpat_wildcard : uni_var -> cmd_pat
| cpat_skip : cmd_pat
| cpat_base_instr : bi_pat -> cmd_pat
| cpat_cond : expr_pat -> cmd_pat -> cmd_pat -> cmd_pat
| cpat_while : expr_pat -> cmd_pat -> cmd_pat
| cpat_seq : cmd_pat -> cmd_pat -> cmd_pat.

Fixpoint match_cmd (cp : cmd_pat) (c : cmd) : uni_env -> M_uni uni_env :=
  fun env =>
  match cp, c with
  | cpat_wildcard x, _ => M_uni_return (VarMap.add x (uni_cmd c) env)
  | cpat_skip, i_skip => M_uni_return env
  | cpat_base_instr bp,
    i_base_instr bi =>
    match_bi bp bi env
  | cpat_cond ep cp1 cp2,
    i_cond e c1 c2 =>
    (
        env1 <-- match_expr ep e env ;;;
        env2 <-- match_cmd cp1 c1 env ;;;
        env3 <-- match_cmd cp2 c2 env ;;;
        env12 <-- uni_env_union env1 env2 ;;;
        uni_env_union env12 env3
      )%M_uni
  | cpat_while ep cp,
    i_while e c =>
    (
        env1 <-- match_expr ep e env ;;;
        env2 <-- match_cmd cp c env ;;;
        uni_env_union env1 env2
      )%M_uni
  | cpat_seq cp1 cp2,
    i_seq c1 c2 =>
    (
        env1 <-- match_cmd cp1 c1 env ;;;
        env2 <-- match_cmd cp2 c2 env ;;;
        uni_env_union env1 env2
      )%M_uni
  | _, _ => inl []
  end.

Definition empty_uni_env := VarMap.empty uni_res.

(* Match the cmd one sequence at a time, until the pattern is exhausted.
   Returns the remaining cmd if any, and the unification environment *)
Fixpoint match_cmd_prefix (cpat : cmd_pat) (c : cmd) : uni_env -> M_uni (uni_env * option cmd) :=
  fun env =>
  match cpat, c with
  | cpat_seq cp1 cp2, i_seq c1 c2 =>
    (env1 <-- match_cmd cp1 c1 env ;;;
     match_cmd_prefix cp2 c2 env1)%M_uni
  | cpat, i_seq c1 c2 =>
    (env1 <-- match_cmd cpat c1 env ;;;
     M_uni_return (env1, Some c2))%M_uni
  | cpat, c =>
    (env1 <-- match_cmd cpat c env ;;;
     M_uni_return (env1, None))%M_uni
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
Definition zpat_wildcard : uni_var -> Z_pat := apat_uni Z.

Coercion str_uni_var : string >-> uni_var.
Coercion epat_wildcard : uni_var >-> expr_pat.
Coercion bipat_wildcard : uni_var >-> bi_pat.
Coercion cpat_wildcard : uni_var >-> cmd_pat.
Coercion ppat_wildcard : uni_var >-> positive_pat.
Coercion vpat_wildcard : uni_var >-> var_pat.
Coercion zpat_wildcard : uni_var >-> Z_pat.

(*Coercion epat_var : var_pat >-> expr_pat.*)
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
  Eval compute in match_cmd ("?x" <$- lap("?w", epv (vpat "y")))%pat ("x" <$- lap(1%positive, "y")) empty_uni_env.

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

  Definition complex_pat2 :=
    ("?idx" <- 0%Z ;;
     While (epv "?idx") :< len(epv "?x") do
       at("?x", epv "?idx") <- ((epv "?y") !! epv "?idx")%pat
     end ;;
     "?x1" <- "?lit"
    )%pat.

  Definition complex_prog2 :=
    ("idx" <- 0%Z ;;
    While ("idx" :< len("x"))%expr do
      at("x", "idx") <- "y" !! "idx"
     end ;;
    "x1" <- 1%Z ;;
    "x2" <- 2%Z
    )%cmd.
  Eval compute in match_cmd complex_pat complex_prog empty_uni_env.
  Eval compute in match_cmd_prefix complex_pat2 complex_prog2 empty_uni_env.
End TestNotation.

Inductive Z_pat_matches: uni_env -> Z_pat -> Z -> Prop :=
| Z_pat_same: forall uenv z,
    Z_pat_matches uenv (zpat z) z
| Z_pat_var: forall uenv ux z,
    VarMap.MapsTo ux (uni_Z z) uenv
    -> Z_pat_matches uenv (zpat_wildcard ux) z.

Lemma match_Z_correct: forall zp z uenv1 uenv2,
    match_Z zp z uenv1 = inr uenv2
    -> Z_pat_matches uenv2 zp z.
Proof.
Admitted.

Inductive positive_pat_matches: uni_env -> positive_pat -> positive -> Prop :=
| positive_pat_same: forall uenv p,
    positive_pat_matches uenv (ppat p) p
| positive_pat_var: forall uenv ux p,
    VarMap.MapsTo ux (uni_positive p) uenv
    -> positive_pat_matches uenv (ppat_wildcard ux) p.

Lemma match_pos_correct: forall pp p uenv1 uenv2,
    match_pos pp p uenv1 = inr uenv2
    -> positive_pat_matches uenv2 pp p.
Proof.
Admitted.

Inductive var_pat_matches: uni_env -> var_pat -> var -> Prop :=
| var_pat_same: forall uenv x,
    var_pat_matches uenv (vpat x) x
| var_pat_var: forall uenv ux x,
    VarMap.MapsTo ux (uni_variable x) uenv
    -> var_pat_matches uenv (vpat_wildcard ux) x.

Lemma match_var_correct: forall vp v uenv1 uenv2,
    match_var vp v uenv1 = inr uenv2
    -> var_pat_matches uenv2 vp v.
Proof.
Admitted.

Inductive expr_pat_matches : uni_env -> expr_pat -> expr -> Prop :=
| expr_wildcard_matches: forall ux uenv e,
    VarMap.MapsTo ux (uni_expr e) uenv
    -> expr_pat_matches uenv (epat_wildcard ux) e
| epat_lit_matches: forall uenv zp z,
    Z_pat_matches uenv zp z
    -> expr_pat_matches uenv (epat_lit zp) (e_lit z)
| epat_var_matches: forall uenv vp v,
    var_pat_matches uenv vp v
    -> expr_pat_matches uenv (epat_var vp) (e_var v)
| epat_add_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_add epl epr) (e_add el er)
| epat_minus_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_minus epl epr) (e_minus el er)
| epat_mult_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_mult epl epr) (e_mult el er)
| epat_div_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_div epl epr) (e_div el er)
| epat_lt_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_lt epl epr) (e_lt el er)
| epat_eq_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_eq epl epr) (e_eq el er)
| epat_and_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_and epl epr) (e_and el er)
| epat_or_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_or epl epr) (e_or el er)
| epat_index_matches: forall uenv epl epr el er,
    expr_pat_matches uenv epl el
    -> expr_pat_matches uenv epl er
    -> expr_pat_matches uenv (epat_index epl epr) (e_index el er)
| epat_length_matches: forall uenv ep e,
    expr_pat_matches uenv ep e
    -> expr_pat_matches uenv (epat_length ep) (e_length e).

Lemma match_expr_correct: forall ep e uenv1 uenv2,
    match_expr ep e uenv1 = inr uenv2
    -> expr_pat_matches uenv2 ep e.
Proof.
Admitted.

Inductive bi_pat_matches: uni_env -> bi_pat -> base_instr -> Prop :=
| bipat_wildcard_matches: forall uenv ux bi,
    VarMap.MapsTo ux (uni_base_instr bi) uenv
    -> bi_pat_matches uenv (bipat_wildcard ux) bi
| bipat_laplace_matches: forall uenv vp v pp p ep e,
    var_pat_matches uenv vp v
    -> positive_pat_matches uenv pp p
    -> expr_pat_matches uenv ep e
    -> bi_pat_matches uenv (bipat_laplace vp pp ep) (bi_laplace v p e)
| bipat_assign_matches: forall uenv vp v ep e,
    var_pat_matches uenv vp v
    -> expr_pat_matches uenv ep e
    -> bi_pat_matches uenv (bipat_assign vp ep) (bi_assign v e)
| bipat_index_assign_matches: forall uenv vp v ep1 e1 ep2 e2,
    var_pat_matches uenv vp v
    -> expr_pat_matches uenv ep1 e1
    -> expr_pat_matches uenv ep2 e2
    -> bi_pat_matches uenv (bipat_index_assign vp ep1 ep2) (bi_index_assign v e1 e2)
| bipat_length_matches: forall uenv vp v ep e,
    var_pat_matches uenv vp v
    -> expr_pat_matches uenv ep e
    -> bi_pat_matches uenv (bipat_length_assign vp ep) (bi_length_assign v e).

Lemma match_bi_correct: forall bip bi uenv1 uenv2,
    match_bi bip bi uenv1 = inr uenv2
    -> bi_pat_matches uenv2 bip bi.
Proof.
Admitted.

Inductive cmd_pat_matches: uni_env -> cmd_pat -> cmd -> Prop :=
| cpat_wildcard_matches: forall uenv ux c,
    VarMap.MapsTo ux (uni_cmd c) uenv
    -> cmd_pat_matches uenv (cpat_wildcard ux) c
| cpat_skip_matches: forall uenv,
    cmd_pat_matches uenv cpat_skip i_skip
| cpat_base_instr_matches: forall uenv bip bi,
    bi_pat_matches uenv bip bi
    -> cmd_pat_matches uenv (cpat_base_instr bip) (i_base_instr bi)
| cpat_cond_matches: forall uenv ep e cp1 c1 cp2 c2,
    expr_pat_matches uenv ep e
    -> cmd_pat_matches uenv cp1 c1
    -> cmd_pat_matches uenv cp2 c2
    -> cmd_pat_matches uenv (cpat_cond ep cp1 cp2) (i_cond e c1 c2)
| cpat_while_matches: forall uenv ep e cp c,
    expr_pat_matches uenv ep e
    -> cmd_pat_matches uenv cp c
    -> cmd_pat_matches uenv (cpat_while ep cp) (i_while e c)
| cpat_seq_matches: forall uenv cp1 cp2 c1 c2,
    cmd_pat_matches uenv cp1 c1
    -> cmd_pat_matches uenv cp2 c2
    -> cmd_pat_matches uenv (cpat_seq cp1 cp2) (i_seq c1 c2).

Lemma match_cmd_correct: forall cp c uenv1 uenv2,
    match_cmd cp c uenv1 = inr uenv2
    -> cmd_pat_matches uenv2 cp c.
Proof.
Admitted.

Lemma match_cmd_prefix_seq_correct: forall cp c1 uenv1 uenv2 c2,
    match_cmd_prefix cp (i_seq c1 c2) uenv1 = inr (uenv2, Some c2)
    -> cmd_pat_matches uenv2 cp c1.
Proof.
Admitted.

Lemma match_cmd_prefix_nonseq_correct: forall cp c uenv1 uenv2,
    match_cmd_prefix cp c uenv1 = inr (uenv2, None)
    -> cmd_pat_matches uenv2 cp c.
Proof.
Admitted.
