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

Notation "a '<-' ma ';;;' p" := (M_uni_bind ma (fun a => p))
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
    (e1' <- M_uni_return e1 ;;;
     e2' <- M_uni_return e2 ;;;
     M_uni_return (e1', e2'))%M_uni.

  Eval compute in test_val.

End TestUnion.

Inductive expr_pat :=
| epat_wildcard : uni_var -> expr_pat
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

Definition match_var (vp : var_pat) (v : var) : uni_env -> M_uni uni_env :=
  fun env =>
  match vp with
  | apat_atom _ v' => if var_eqdec v v'
                   then M_uni_return env
                   else inl []
  | apat_uni _ uv => M_uni_return (VarMap.add uv (uni_variable v) env)
  end.

Fixpoint match_expr (ep : expr_pat) (e : expr) : uni_env -> M_uni uni_env :=
  fun env =>
    match ep, e with
    | epat_wildcard x, _ => M_uni_return (VarMap.add x (uni_expr e) env)
    | epat_var vp, e_var v => (
        env' <- match_var vp v env ;;;
        M_uni_return env'
      )%M_uni
    | epat_add ep1 ep2, e_add e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_minus ep1 ep2, e_minus e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_mult ep1 ep2, e_mult e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_div ep1 ep2, e_div e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_lt ep1 ep2, e_lt e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_eq ep1 ep2, e_eq e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_and ep1 ep2, e_and e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_or ep1 ep2, e_or e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_index ep1 ep2, e_index e1 e2 => (
        env1 <- match_expr ep1 e1 env ;;;
        env2 <- match_expr ep2 e2 env ;;;
        uni_env_union env1 env2
      )%M_uni
    | epat_length ep1, e_length e1 =>
        match_expr ep1 e1 env
    | _, _ => inl []
    end.

Inductive bi_pat :=
| bipat_wildcard : uni_var -> bi_pat
| bipat_laplace : var_pat -> positive_pat -> expr_pat -> bi_pat
| bipat_index_assign : var_pat -> expr_pat -> expr_pat -> bi_pat
| bipat_length_assign : var_pat -> expr_pat -> bi_pat.

Inductive cmd_pat :=
| cpat_wildcard : uni_var -> cmd_pat
| cpat_base_instr : bi_pat -> cmd_pat
| cpat_cond : expr_pat -> cmd_pat -> cmd_pat -> cmd_pat
| cpat_while : expr_pat -> cmd_pat -> cmd_pat
| cpat_seq : cmd_pat -> cmd_pat -> cmd_pat.