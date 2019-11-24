(** Proof that the interval in cartesian cubical sets is tiny *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.terminal.
Require Import UniMath.CategoryTheory.exponentials.
Require Import UniMath.CategoryTheory.Presheaf.
Require Import UniMath.CategoryTheory.whiskering.
Require Import UniMath.CategoryTheory.opp_precat.
Require Import UniMath.CategoryTheory.FunctorCategory.
Require Import UniMath.CategoryTheory.RightKanExtension.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.limits.graphs.limits.
Require Import UniMath.CategoryTheory.categories.HSET.Core.
Require Import UniMath.CategoryTheory.categories.HSET.Limits.
Require Import UniMath.CategoryTheory.yoneda.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.categories.HSET.Structures.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.Type.Structures.
Require Import UniMath.Foundations.Sets.

Open Scope stn.

(* Construction of cartesian cube category using nat as object set *)

Definition cube_precategory_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor nat (λ (m n : nat), ⟦n⟧ → ⟦m⟧ ⨿ ⟦2⟧).

Definition cube_precategory_data : precategory_data.
Proof.
  exists cube_precategory_ob_mor.
  split.
  - intro n.
    exact (λ (i : ⟦n⟧), inl i).
  - intros l m n f g i.
    induction (g i) as [a | b].
    + exact (f a).
    + exact (inr b).
Defined.

Definition cube_precategory : precategory.
Proof.
  exists cube_precategory_data.
  use make_is_precategory_one_assoc.
  - intros m n f.
    apply funextfun.
    intro i.
    cbn.
    now induction (f i).
  - intros m n g.
    apply idpath.
  - intros k l m n f g h.
    apply funextfun.
    intro i.
    cbn.
    now induction (h i).
Defined.

Definition cube_category : category.
Proof.
  exists cube_precategory.
  intros m n.
  apply funspace_isaset.
  apply isfinite_isaset.
  apply isfinitecoprod; apply isfinitestn.
Defined.

(* Construction of binary product *)

Lemma stn_left_to_coprod (m n : nat) (i : ⟦ m ⟧) :
  weqfromcoprodofstn_invmap m n (stn_left m n i) = inl i.
Proof.
  now rewrite <- weqfromcoprodofstn_eq1.
Defined.

Lemma stn_right_to_coprod (m n : nat) (i : ⟦ n ⟧) :
  weqfromcoprodofstn_invmap m n (stn_right m n i) = inr i.
Proof.
  now rewrite <- weqfromcoprodofstn_eq1.
Defined.

Definition cube_category_binproduct : BinProducts cube_category.
Proof.
  intros m n.
  use make_BinProduct.
  - exact (m + n).
  - exact (λ i : ⟦m⟧, inl (stn_left m n i)).
  - exact (λ i : ⟦n⟧, inl (stn_right m n i)).
  - use make_isBinProduct.
    + apply homset_property.
    + intros l f g.
      use unique_exists.
      * intro i.
        induction (weqfromcoprodofstn_invmap m n i) as [ x1 | x2 ].
        -- exact (f x1).
        -- exact (g x2).
      * cbn.
        split; apply funextfun; intro i.
        -- now rewrite stn_left_to_coprod.
        -- now rewrite stn_right_to_coprod.
      * intro h.
        now apply isapropdirprod; apply homset_property.
      * intros h [H1 H2].
        apply funextfun.
        intros i.
        rewrite <- (maponpaths h (weqfromcoprodofstn_eq2 m n i)).
        induction (weqfromcoprodofstn_invmap m n i) as [x1 | x2].
        -- now rewrite <- H1.
        -- now rewrite <- H2.
Defined.

(* Construction of cubical set *)

Lemma zero_is_terminal : Terminal cube_category.
Proof.
  use make_Terminal.
  - exact 0.
  - use make_isTerminal.
    intro n.
    apply iscontrfunfromempty2.
    use weqstn0toempty.
Defined.

Definition prod_functor : functor cube_category cube_category
  := constprod_functor2 cube_category_binproduct 0.

Open Scope cat.

Definition cubical_sets : precategory := [cube_category^op, HSET, has_homsets_HSET].

Definition precomp_functor : functor cubical_sets cubical_sets.
Proof.
  use pre_composition_functor.
  - apply has_homsets_opp.
    apply homset_property.
  - apply functor_opp.
    exact prod_functor.
Defined.

Lemma precomp_functor_has_right_adjoint : is_left_adjoint precomp_functor.
Proof.
  apply RightKanExtension_from_limits.
  apply LimsHSET.
Defined.

Definition y : cube_category ⟶ cubical_sets := yoneda cube_category (homset_property cube_category).

Definition I : cubical_sets := y 0.

Definition cubical_sets_binproduct : BinProducts cubical_sets := BinProducts_PreShv.

Definition cubical_sets_exponentials : Exponentials cubical_sets_binproduct.
Proof.
  use Exponentials_functor_HSET.
  use has_homsets_opp.
  exact (homset_property cube_category).
Defined.

Definition exp_I : functor cubical_sets cubical_sets := pr1 (cubical_sets_exponentials I).

Definition cubical_homsets : has_homsets cubical_sets.
Proof.
  use functor_category_has_homsets.
Defined.

Lemma first_iso (F : cubical_sets) (X : cube_category^op) :
  (pr1hSet (pr1 (exp_I F) X)) ≃ (cubical_sets ⟦y X, exp_I F⟧).
Proof.
  use invweq.
  exact (yoneda_weq cube_category (homset_property cube_category) X (exp_I F)).
Defined.

Lemma second_iso (F : cubical_sets) (X : cube_category^op) : cubical_sets ⟦y X, exp_I F⟧ ≃ cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧.
Proof.
  use invweq.
  set (adj := pr2 (cubical_sets_exponentials I)).
  change (pr1 (cubical_sets_exponentials I)) with exp_I in adj.
  exact (adjunction_hom_weq adj (y X) F).
Defined.

(* Lemma yon_comm_w_binprod (C : category) (C_binproduct : BinProducts C) : *)
(*   ∏ (X Y : C), *)
(*   iso (yoneda C (homset_property C) (constprod_functor1 C_binproduct X Y)) *)
(*       (constprod_functor1 BinProducts_PreShv (yoneda C (homset_property C) X) (yoneda C (homset_property C) Y)). *)
(* Admitted. *)

Lemma third_iso (F : cubical_sets) (X : cube_category^op) : cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧ ≃ cubical_sets ⟦y (constprod_functor1 cube_category_binproduct X 0), F⟧.
Proof.
Admitted.

Lemma fourth_iso (F : cubical_sets) (X : cube_category^op) : cubical_sets ⟦y (constprod_functor1 cube_category_binproduct X 0), F⟧ ≃ (pr1hSet (pr1 (precomp_functor F) X)).
Proof.
  set (T := pr1 (precomp_functor F)).
  unfold cubical_sets in T.
  set (H := yoneda_weq cubical_sets cubical_homsets (y (constprod_functor1 cube_category_binproduct X 0)) (precomp_functor F)).
  unfold cubical_sets.

(* Lemma pointwise_iso_to_iso : (∏ (F : cubical_sets) (X : cube_category^op), (pr1 (precomp_functor F)) X ≃ (exp_I F) X) → nat_iso precomp_functor exp_I. *)
(* (* functor_iso_from_pointwise_iso *) *)
(* Admitted. *)

About functor_iso_from_pointwise_iso.

Lemma exp_I_iso_precomp_functor : nat_iso precomp_functor exp_I.
Proof.
  (* apply pointwise_iso_to_iso. *)
Admitted.

Theorem I_is_tiny : is_left_adjoint exp_I.
Proof.
  use is_left_adjoint_iso.
  - apply homset_property.
  - exact precomp_functor.
  - exact (nat_iso_to_iso precomp_functor exp_I exp_I_iso_precomp_functor).
  - exact precomp_functor_has_right_adjoint.
Defined.


Lemma weq_to_iso {C : category} (X Y : C) : (pr1set X ≃ Y) -> (iso X Y).
