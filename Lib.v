Require Import Coq.Classes.Morphisms.

Require Import Coq.Reals.Reals.
Require Import Fourier.

Require Import Random.Prelude.
Require Import Random.Prog.
Require Import Random.Ubase.
Require Import Random.Carac.

Require Import Program.

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

Module Type Laplace(E : Embedding).
  Module EImpl := E.
  Module CARImpl := CaracFun(EImpl).
  Import CARImpl RP PP MP UP EImpl.

  (* The range of d is in P *)
  Definition range {A} (P : A -> Prop) (d : distr A) :=
    forall f, (forall x, P x -> 0 == f x) -> 0 == mu d f.

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

  Parameter Laplace : forall (eps:R), (0 < eps)%R -> Z -> distr Z.

  Parameter Laplace_ratio : forall (eps:R) a a' b (H : (0 < eps)%R),
      (iR (mu (Laplace eps H a)  (fun k => if Zeq_bool k b then 1%U else 0)%U) <=
       iR (mu (Laplace eps H a') (fun k => if Zeq_bool k b then 1%U else 0)%U) *
       (exp(eps * Rabs(IZR a - IZR a'))))%R.

  Parameter Laplace_lossless: forall (eps:R) a (H : (0 < eps)%R),
      (mu (Laplace eps H a) (fun k => 1%U) == 1)%U.

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

Ltac inv H := inversion H; subst; clear H.
