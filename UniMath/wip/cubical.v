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
Require Import UniMath.CategoryTheory.categories.HSET.MonoEpiIso.

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
  := constprod_functor1 cube_category_binproduct 0.

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

Lemma first_iso (F : cubical_sets) (X : cube_category) :
  iso (pr1 (exp_I F) X) (make_hSet (cubical_sets ⟦y X, exp_I F⟧) (cubical_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use invweq.
  use yoneda_weq.
Defined.

Lemma second_iso (F : cubical_sets) (X : cube_category) : @iso HSET (make_hSet (cubical_sets ⟦y X, exp_I F⟧) (cubical_homsets _ _)) (make_hSet (cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧) (cubical_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use invweq.
  use adjunction_hom_weq.
  exact (pr2 (cubical_sets_exponentials I)).
Defined.

Lemma yon_comm_w_binprod {C : category} (PC : BinProducts C) :
  ∏ (X Y : C),
  iso (yoneda _ (homset_property _) (BinProductObject _ (PC X Y)))
      (BinProductObject (PreShv _) (BinProducts_PreShv (yoneda _ (homset_property _) X) (yoneda _ (homset_property _) Y))).
Proof.
  intros X Y.
  set (y := yoneda _ _).
  use make_iso.
  - use make_nat_trans.
    + intros Z f.
      constructor.
      * exact (f · BinProductPr1 _ _).
      * exact (f · BinProductPr2 _ _).
    + intros Z W f.
      use funextfun.
      intro g.
      cbn.
      admit.
  - use is_iso_from_is_z_iso.
    use make_is_z_isomorphism.
    + use make_nat_trans.
      * intros Z [f1 f2].
        exact (BinProductArrow _ (PC X Y) f1 f2).
      * intros Z W f.
        use funextfun.
        intro g.
        cbn.
        admit.
    + apply tpair.
      * admit.
      * admit.
Admitted.

Lemma third_iso (F : cubical_sets) (X : cube_category) : @iso HSET (make_hSet (cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧) (cubical_homsets _ _)) (make_hSet (cubical_sets ⟦y (constprod_functor1 cube_category_binproduct 0 X), F⟧) (cubical_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use iso_comp_right_weq.
  use yon_comm_w_binprod.
Defined.

Lemma fourth_iso (F : cubical_sets) (X : cube_category) : @iso HSET (make_hSet (cubical_sets ⟦y (constprod_functor1 cube_category_binproduct 0 X), F⟧) (cubical_homsets _ _)) (pr1 (precomp_functor F) X).
Proof.
  use hset_equiv_iso.
  use yoneda_weq.
Defined.

Lemma total_iso (F : cubical_sets) (X : cube_category) : iso (pr1 (exp_I F) X) (pr1 (precomp_functor F) X).
Proof.
  use iso_comp.
  - exact (make_hSet (cubical_sets ⟦y X, exp_I F⟧) (cubical_homsets _ _)).
  - apply first_iso.
  - use iso_comp.
    + exact (make_hSet (cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧) (cubical_homsets _ _)).
    + apply second_iso.
    + use iso_comp.
      * exact (make_hSet (cubical_sets ⟦y (constprod_functor1 cube_category_binproduct 0 X), F⟧) (cubical_homsets _ _)).
      * apply third_iso.
      * apply fourth_iso.
Defined.

(* Arguments Exponentials_functor_HSET : simpl never. *)

Lemma make_nat_trans_from_two_lv_iso {C : category} (F G : functor [C^op,SET] [C^op,SET])
      (lv2_iso : ∏ X x, iso (pr1 (F X) x) (pr1 (G X) x))
      (lv2_nat_trans : ∏ X, is_nat_trans _ _ (λ x, lv2_iso X x))
      (lv1_nat_trans : is_nat_trans F G (λ X, make_nat_trans _ _ _ (lv2_nat_trans X))) :
  [[C^op, SET], [C^op, SET]] ⟦ F, G ⟧.
Proof.
  use make_nat_trans.
    + intros X.
      use make_nat_trans.
      * intros x.
        exact (lv2_iso X x).
      * use lv2_nat_trans.
    + exact lv1_nat_trans.
Defined.

Lemma iso_from_two_lv_iso {C : category} (F G : functor [C^op,SET] [C^op,SET])
      (lv2_iso : ∏ X x, iso (pr1 (F X) x) (pr1 (G X) x))
      (lv2_nat_trans : ∏ X, is_nat_trans _ _ (λ x, lv2_iso X x))
      (lv1_nat_trans : is_nat_trans F G (λ X, make_nat_trans _ _ _ (lv2_nat_trans X))) :
      @iso [[C^op, SET], [C^op, SET]] F G.
Proof.
  use make_iso.
  - exact (make_nat_trans_from_two_lv_iso F G lv2_iso lv2_nat_trans lv1_nat_trans).
  - use is_iso_from_is_z_iso.
    use make_is_z_isomorphism.
    + use make_nat_trans_from_two_lv_iso.
      * intros X x.
        exact (iso_inv_from_iso (lv2_iso X x)).
      * abstract (intros X x y f;
                  apply pathsinv0, iso_inv_on_left; rewrite <- assoc;
                  now apply pathsinv0, iso_inv_on_right, (lv2_nat_trans X)).
      * abstract (intros X Y α;
                  apply nat_trans_eq; [ apply homset_property|];
                  intro x; simpl;
                  apply pathsinv0, (iso_inv_on_left _ _ _ _ _ (lv2_iso Y x));
                  rewrite <- assoc; apply pathsinv0, iso_inv_on_right;
                  exact (eqtohomot (maponpaths pr1 (lv1_nat_trans X Y α)) x)).
    + abstract (use make_is_inverse_in_precat;
      [ apply nat_trans_eq; [ apply homset_property |]; intro X;
        apply nat_trans_eq; [ apply homset_property |]; intro x;
        exact (iso_inv_after_iso (lv2_iso X x))
      | apply nat_trans_eq; [ apply homset_property |]; intro X;
        apply nat_trans_eq; [ apply homset_property |]; intro x;
        apply funextsec; intros y;
        exact (eqtohomot (iso_after_iso_inv (lv2_iso X x)) y) ]).
Defined.

Lemma exp_I_iso_precomp_functor : @iso [[cube_category^op, SET], [cube_category^op, SET]]  precomp_functor exp_I.
Proof.
  use iso_from_two_lv_iso.
(*   use foo. *)
(*   use (@iso_to_nat_iso (cubical_sets,,_) (cubical_sets,,_) precomp_functor exp_I). *)
(*   admit. *)
(*   admit. *)
(*   use functor_iso_from_pointwise_iso. *)

(*   - *)
(* use make_nat_trans. *)
(* + *)
(*   intros F. *)
(* use make_nat_trans. *)
(* * *)
(*   intros X. *)
(*   admit. *)
(*   * *)
(* intros x y f. *)
(* admit. *)
(* + intros F G a. *)
(* admit. *)
(*   - intros F. *)
(*     Print is_z_isomorphism. *)
(* simpl. *)
Admitted.

Theorem I_is_tiny : is_left_adjoint exp_I.
Proof.
  use is_left_adjoint_iso.
  - apply cubical_homsets.
  - exact precomp_functor.
  - exact exp_I_iso_precomp_functor.
  - exact precomp_functor_has_right_adjoint.
Defined.
