Require Export Cfuzzi.Syntax.
Require Export Cfuzzi.IncExt.
Require Export Cfuzzi.DecExt.

Module KitchenSink(E : Embedding) (Lap: Laplace E) (LOGIC: APRHL E Lap).

  Module Inc := Increment E Lap LOGIC.
  Module Dec := Decrement E Lap LOGIC.
  Import Dec TSImpl APRHLImpl.
  Import Inc TSImpl APRHLImpl.

  Definition x := "x"%string.
  Definition y := "y"%string.

  Definition prog :=
    (x <- el 1%Z ;;
      y <- el 2%Z ;;
      inc_cmd x ;;
      dec_cmd x)%cmd.

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
      apply Dec.typing_rule_sens with (tctx := ctx) (pre := sctx) (post := sctx); auto.
      exists 1%Z; auto.
      apply VarMap.find_1; auto.
    Admitted.

End KitchenSink.
