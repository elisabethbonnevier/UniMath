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

Definition cubical_sets : category := PreShv cube_category.

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

Definition I : cubical_sets := yoneda cube_category (pr2 cube_category) 0.

Definition cubical_sets_binproduct : BinProducts cubical_sets.
Proof.
  use BinProducts_functor_precat.
  exact BinProductsHSET.
Defined.

Definition cubical_sets_exponentials : Exponentials cubical_sets_binproduct.
Proof.
  use Exponentials_functor_HSET.
  apply has_homsets_opp.
  apply homset_property.
Defined.

Definition exp_I : functor cubical_sets cubical_sets.
Proof.
  exact (pr1 (cubical_sets_exponentials I)).
Defined.

(* UniMath.CategoryTheory.Core.NaturalTransformations.nat_iso definition of natural isomorphism between functors *)
Search "bijection".
Check precomp_functor.
Print cubical_sets.
About (ob cubical_sets).

Lemma pointwise_iso_to_iso : (∏ (F : cubical_sets) (X : cube_category ^op), weq ((precomp_functor F) X) (exp_I F) X) → nat_iso precomp_functor exp_I.

Lemma exp_I_iso_precomp_functor : nat_iso precomp_functor exp_I.
Proof.
  use functor_iso_from_pointwise_iso.
  -
  use make_iso.
  - admit.
  - use functor_iso_if_pointwise_iso.

Search is_left_adjoint iso.

Theorem tinyI : is_left_adjoint exp_I.
Proof.
  use is_left_adjoint_iso.
  - apply homset_property.
  - exact precomp_functor.
  - exact exp_I_iso_precomp_functor.
  - exact precomp_functor_has_right_adjoint.
Defined.