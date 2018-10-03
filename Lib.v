Require Export Coq.Classes.Morphisms.

Require Export Coq.Reals.Reals.
Require Export Fourier.

Require Export Random.Prelude.
Require Export Random.Prog.
Require Export Random.Ubase.

Require Export Program.

Module Type Embedding.
Include Universe.

Parameter iR : U -> R.
Parameter iU : R -> U.
Parameter retract_U : forall u:U, (iU (iR u) == u)%U.
Parameter retract_R : forall x:R, (0 <= x <= 1)%R -> iR (iU x) = x.
Parameter iR_le : forall u v:U, (u <= v)%U -> (iR u <= iR v)%R.
 (* iU truncates *)
Parameter iU_le : forall x y:R, (x <= y)%R -> (iU x <= iU y)%U.
Parameter iR_0 : iR 0 = 0%R.
Parameter iR_1 : iR 1%U = 1%R.
Parameter iR_lub : forall (f: nat -> U) (H:has_ub (fun k => iR (f k))),
  iR (lub f) = SeqProp.lub (fun k => iR (f k)) H.
Parameter iR_plus : forall u v:U, iR (u + v)%U = Rmin 1 (iR u + iR v).
Parameter iR_mult : forall u v:U, iR (u * v)%U = (iR u * iR v)%R.
Parameter iR_inv : forall u:U, iR ([1-] u) = (1 - iR u)%R.
End Embedding.

Module Laplace (E: Embedding).

Import E.
Module RP := Rules(E).
Import RP.
Import RP.PP.
Import RP.PP.MP.
Import RP.PP.MP.UP.

(* The range of d is in P *)
Definition range {A} (P : A -> Prop) (d : distr A) :=
  forall f, (forall x, P x -> 0 == f x) -> 0 == mu d f.

(* Lift a relation to a product distribution *)
Section Lifting.
  Variable A B : Type.

  Variable P Q: A -> B -> Prop.

  Hypothesis Pdec: forall x y, {P x y} + {~P x y}.

  Definition prodP := fun xy => P (fst xy) (snd xy).

  Definition caracF := fun xy => if Pdec (fst xy) (snd xy) then 1 else 0.

  Definition Fimp2 := forall x y, P x y -> Q x y.
End Lifting.

Arguments prodP {_ _} _.

Record lifting (A B : Type) (R : A -> B -> Prop) (d : distr (A * B))
       (d1 : distr A) (d2 : distr B) : Type :=
  {
    lift_proj1 : forall f, mu d (fun x => f (fst x)) == mu d1 f;
    lift_proj2 : forall f, mu d (fun x => f (snd x)) == mu d2 f;
    lift_range : range (prodP R) d;
  }.

Section LaplaceDistr.

  Local Close Scope nat_scope.
  Local Close Scope U_scope.
  Local Open Scope Z_scope.
  Local Open Scope R_scope.

  Variable eps: R.
  Hypothesis eps_pos: (0 < eps)%R.

  Definition f (a b:Z) : R := exp(-eps * Rabs(IZR a - IZR b)).
  Definition delta (a a': Z) := exp(eps * Rabs(IZR a - IZR a')).

  Lemma f_pos : forall a b, (0 <= f a b)%R.
  Proof.
    intros; apply Rlt_le; apply exp_pos.
  Qed.

  Lemma delta_sym : forall a a', delta a a' = delta a' a.
  Proof.
    intros; unfold delta.
    rewrite Rabs_minus_sym; trivial.
  Qed.

  Lemma delta_pos : forall a a', (0 <= delta a a')%R.
  Proof.
    intros; apply Rlt_le; apply exp_pos.
  Qed.

  Lemma f_notnul : forall a, exists b, (0 < f a b)%R.
  Proof.
    intros; exists 0%Z; apply exp_pos.
  Qed.

  Lemma exp_monotonic : forall x y, (x <= y)%R -> (exp x <= exp y)%R.
  Proof.
    intros.
    apply Rle_lt_or_eq_dec in H; destruct H.
    apply Rlt_le; apply exp_increasing; trivial.
    subst; apply Rle_refl.
  Qed.

  Lemma f_diff_bounded : forall a a' x, (f a x <= delta a a' * f a' x)%R.
  Proof.
    intros; unfold f, delta.
    rewrite <-exp_plus.
    replace (IZR a - IZR x) with (IZR a' - IZR x - (IZR a' - IZR a)) by field.
    replace (eps * Rabs (IZR a - IZR a') + - eps * Rabs (IZR a' - IZR x)) with
        (- (eps * (Rabs (IZR a' - IZR x) - Rabs (IZR a - IZR a')))) by field.
    rewrite Ropp_mult_distr_l_reverse, exp_Ropp, exp_Ropp.
    apply Rle_Rinv; [apply exp_pos | apply exp_pos | ].
    apply exp_monotonic.
    apply Rmult_le_compat_l; [fourier | ].
    rewrite (Rabs_minus_sym (IZR a)).
    apply Rabs_triang_inv.
  Qed.

  Definition Laplace : Z -> distr Z.
  Admitted.

  Lemma Laplace_ratio : forall a a' b,
  iR (mu (Laplace a)  (fun k => if Zeq_bool k b then 1%U else 0)%U) <=
  iR (mu (Laplace a') (fun k => if Zeq_bool k b then 1%U else 0)%U) *
  (delta a a').
  Admitted.

  Lemma Laplace_lossless: forall a,
      (mu (Laplace a) (fun k => 1%U) == 1)%U.
  Admitted.

End LaplaceDistr.


Add Parametric Morphism A : (@mu A) with signature
    (@eq_distr A) ==> (@feq A) ==> (Ueq) as mu_proper.
  intros x y Heq f g Hfeq.
  unfold feq in Hfeq.
  apply Ueq_trans with (y := mu x g).
  unfold eq_distr in Heq.
  - apply mu_stable_eq; auto.
  - apply Heq.
Qed.

Definition Mdistr0 {A : Type} : M A := fun _ => 0.
Hint Unfold Mdistr0.

Definition distr0 {A : Type} : distr A.
  apply Build_distr with (mu := Mdistr0).
  - unfold stable_inv.
    intros f; unfold Mdistr0; simpl; auto.
  - unfold stable_plus.
    intros f g Hfg; unfold Mdistr0; simpl; auto.
  - unfold stable_mult.
    intros k f; unfold Mdistr0; simpl; auto.
  - unfold monotonic.
    intros f g Hfg; unfold Mdistr0; simpl; auto.
Defined.

Lemma Mlet_range_comp : forall {A} (P : A -> Prop) m f,
    range P m
    -> (forall x, P x -> range P (f x))
    -> range P (Mlet m f).
Proof.
  intros A P m f Hm Hf.
  intros g Hg.
  simpl; unfold star, unit.
  unfold range in Hf.
  unfold range in Hm.
  rewrite <- Hm; auto.
Qed.

Lemma range_impl : forall {A} (P Q : A -> Prop) m,
    range P m
    -> (forall x, P x -> Q x)
    -> range Q m.
Proof.
  intros A P Q m HP Himpl.
  unfold range in *.
  intros f Hf.
  rewrite <- HP; auto.
Qed.

Definition iff1 {A} (P Q : A -> Prop) :=
  forall x, P x <-> Q x.

Add Parametric Morphism A : (@range A)
    with signature (@iff1 A) ==> (@eq_distr A) ==> (fun P Q => P <-> Q) as range_compat.
Proof.
  intros P Q HPQ m n Hmn.
  split.
  - intros HP.
    intros f Hf.
    unfold range in *.
    rewrite HP; auto.
    unfold iff1 in HPQ.
    intros x HPx.
    rewrite <- Hf; auto.
    apply HPQ; auto.
  - intros HQ.
    intros f Hf.
    unfold range in *.
    rewrite HQ; auto.
    intros x HQx.
    rewrite <- Hf; auto.
    apply HPQ; auto.
Qed.

End Laplace.

Definition lift_option {A B} (f : A -> B) : option A -> option B :=
  fun oa => match oa with
            | Some a => Some (f a)
            | None => None
            end.

Definition lift_option2 {A B C} (f : A -> B -> C) : option A -> option B -> option C :=
  fun oa ob => match oa, ob with
            | Some a, Some b => Some (f a b)
            | _, _ => None
            end.
