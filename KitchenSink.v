Require Export Syntax.
Require Export IncExt.
Require Export DecExt.

Module KitchenSink(E : Embedding).

  Module Inc := Increment(E).
  Module Dec := Decrement(E).
  Import Dec TS APRHL.
  Import Inc TS APRHL.

  Definition x := "x"%string.
  Definition y := "y"%string.

  Definition prog :=
    x <- el 1%Z ;;
      y <- el 2%Z ;;
      inc_cmd x ;;
      dec_cmd x.

  Goal forall ctx, VarMap.MapsTo x t_int ctx ->
                   VarMap.MapsTo y t_int ctx ->
                   welltyped ctx prog.
    intros ctx Hx Hy.
    repeat apply welltyped_seq; auto.
    apply welltyped_assign with (t := t_int); auto.
    apply welltyped_assign with (t := t_int); auto.
    apply Inc.typing_rule_type; auto.
    apply Dec.typing_rule_type; auto.
  Qed.

  Goal forall ctx sctx,
      welltyped ctx prog ->
      VarMap.MapsTo x 1%Z sctx ->
      (prog ~_(0%R) prog : denote_env sctx ==> denote_env sctx)%triple.
    intros ctx sctx Htyped Hsens_typed.
    unfold prog; inversion Htyped; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H7; subst.
    replace 0%R with (0 + 0)%R.
    apply aprhl_seq with (env := ctx) (env' := ctx) (Q := denote_env sctx); auto.
    Focus 2.
    replace 0%R with (0 + 0)%R.
    apply aprhl_seq with (env := ctx) (env' := ctx) (Q := denote_env sctx); auto.
    Focus 2.
    replace 0%R with (0 + 0)%R.
    apply aprhl_seq with (env := ctx) (env' := ctx) (Q := denote_env sctx); auto.
    apply Inc.typing_rule_sens with (tctx := ctx) (pre := sctx) (post := sctx); auto.
    - simpl.
      exists 1%Z; auto.
      apply VarMap.find_1; auto.
      Focus 2.
      (* Blows up because of transparency issues, TODO: fix this by adding
         module types to everything with clear access paths annotating equality of
         important types *)
    Fail apply Dec.typing_rule_sens with (tctx := ctx) (pre := sctx) (post := sctx); auto.
    Admitted.

End KitchenSink.
