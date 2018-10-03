Require Export SyntaxExtension.

Module Increment(E : Embedding) <: Extension(E).

  Module TS := TypeSystem.TypeSystem(E).

  Import TS.
  Import TS.APRHL.

  Inductive inc_syntax :=
  | inc_cmd : var -> inc_syntax.

  Definition syntax := inc_syntax.

  (* This seems necessary for Coq to see the path inc_syntax -> syntax -> cmd *)
  Definition inc_syntax_to_syntax : inc_syntax -> syntax := fun x => x.
  Coercion inc_syntax_to_syntax : inc_syntax >-> syntax.

  Definition compile (c : syntax) :=
    match c with
    | inc_cmd x =>
      (x <- (ev x) :+ (el 1%Z))
    end.

  Coercion compile : syntax >-> cmd.

  Definition inc_var (c : syntax) :=
    match c with
    | inc_cmd x => x
    end.

  Definition premises_type (tctx : st_env) (c : syntax) :=
    [ VarMap.MapsTo (inc_var c) t_int tctx ]%list.

  Lemma typing_rule_type:
    forall tctx c,
      let c' := compile c in
      uncurry_P (premises_type tctx c) (welltyped tctx c').
  Proof.
    intros tctx c.
    destruct c as [x]; simpl.
    intros H.
    apply welltyped_assign with (t := t_int); auto.
  Qed.

  Definition premises_sens (tctx : st_env) (pre: env) (c: syntax) (post: env) (eps: R) :=
    [ pre = post;
        exists d, env_get (inc_var c) post = Some d;
        welltyped tctx (compile c);
        (eps = 0)%R
    ].

  Lemma typing_rule_sens:
    forall tctx pre c post eps,
      let c' := compile c in
      uncurry_P
        (premises_sens tctx pre c post eps)
        (c' ~_(eps) c' : denote_env pre ==> denote_env post)%triple.
  Proof.
    intros tctx pre c post eps.
    destruct c as [x]; simpl.
    intros Hx_sens [sens Hsens] Htyped Heps; subst.
    inversion Htyped; subst; clear Htyped.
    inversion H3; subst; clear H3.
    apply aprhl_conseq
      with (Q' := denote_env (env_update x post (env_get x post)))
           (env1 := tctx) (env2 := tctx)
           (P' := denote_env post) (eps' := 0%R); auto.
    - apply welltyped_assign with (t := t_int); auto.
    - apply welltyped_assign with (t := t_int); auto.
    - rewrite Hsens.
      apply assign_sound.
      simpl; auto.
      rewrite Hsens; simpl.
      f_equal; omega.
    - intros m1 m2.
      rewrite Hsens.
      apply env_update_impl with (d' := sens); auto.
      omega.
    - fourier.
  Qed.

End Increment.
