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
  make_precategory_ob_mor nat (λ m n : nat, ⟦n⟧ → ⟦m⟧ ⨿ ⟦2⟧).

Definition cube_precategory_data : precategory_data.
Proof.
  exists cube_precategory_ob_mor.
  split.
  - intro n.
    exact (λ i : ⟦n⟧, inl i).
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
    apply funextfun; intro i.
    cbn.
    now induction (f i).
  - intros m n g.
    apply idpath.
  - intros k l m n f g h.
    apply funextfun; intro i.
    cbn.
    now induction (h i).
Defined.

Definition cube_category : category.
Proof.
  exists cube_precategory.
  intros m n.
  apply funspace_isaset, isfinite_isaset.
  apply isfinitecoprod; apply isfinitestn.
Defined.

(* Construction of binary products in cube_category *)

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
        apply funextfun; intros i.
        rewrite <- (maponpaths h (weqfromcoprodofstn_eq2 m n i)).
        induction (weqfromcoprodofstn_invmap m n i) as [x1 | x2].
        -- now rewrite <- H1.
        -- now rewrite <- H2.
Defined.

(* Construction of cubical sets *)

Lemma zero_is_terminal : Terminal cube_category.
Proof.
  exists 0.
  intro n.
  apply iscontrfunfromempty2.
  use weqstn0toempty.
Defined.

Definition prod_functor : functor cube_category cube_category
  := constprod_functor1 cube_category_binproduct 0.

Open Scope cat.

Definition cubical_sets : category := [cube_category^op, SET].

Definition precomp_functor : functor cubical_sets cubical_sets.
Proof.
  use pre_composition_functor.
  - apply has_homsets_opp, homset_property.
  - apply functor_opp.
    exact prod_functor.
Defined.

Lemma precomp_functor_has_right_adjoint : is_left_adjoint precomp_functor.
Proof.
  apply RightKanExtension_from_limits.
  apply LimsHSET.
Defined.

Definition y : cube_category ⟶ cubical_sets :=
  yoneda cube_category (homset_property cube_category).

Definition I : cubical_sets := y 0.

Definition cubical_sets_binproduct : BinProducts cubical_sets := BinProducts_PreShv.

Definition cubical_sets_exponentials : Exponentials cubical_sets_binproduct.
Proof.
  use Exponentials_functor_HSET.
  use has_homsets_opp.
  apply homset_property.
Defined.

Definition exp_I : functor cubical_sets cubical_sets := pr1 (cubical_sets_exponentials I).

Definition cubical_homsets : has_homsets cubical_sets := homset_property cubical_sets.

Definition yon_comm_w_binprod_nat_trans_data {C : category} (PC : BinProducts C) (X Y : C) :
  nat_trans_data (pr1 (yoneda C (homset_property C) (BinProductObject C (PC X Y))))
            (pr1 (BinProductObject [C^op, HSET, has_homsets_HSET]
                                   (BinProducts_PreShv (yoneda C (homset_property C) X) (yoneda C (homset_property C) Y)))).
Proof.
  intros Z f.
  split; [exact (f · BinProductPr1 _ _) | exact (f · BinProductPr2 _ _)].
Defined.

Lemma is_nat_trans_yon_comm_w_binprod {C : category} (PC : BinProducts C) (X Y : C) :
  is_nat_trans _ _ (yon_comm_w_binprod_nat_trans_data PC X Y).
Proof.
  intros Z W f.
  use funextfun; intro g.
  use dirprodeq.
  - exact (assoc' (f : C ⟦W, Z⟧) (g : C ⟦Z, BinProductObject C (PC X Y)⟧) (BinProductPr1 C (PC X Y))).
  - exact (assoc' (f : C ⟦W, Z⟧) (g : C ⟦Z, BinProductObject C (PC X Y)⟧) (BinProductPr2 C (PC X Y))).
Qed.

Definition yon_comm_w_binprod_nat_trans {C : category} (PC : BinProducts C) (X Y : C) :
  nat_trans (pr1 (yoneda C (homset_property C) (BinProductObject C (PC X Y))))
            (pr1 (BinProductObject [C^op, HSET, has_homsets_HSET]
                                   (BinProducts_PreShv (yoneda C (homset_property C) X) (yoneda C (homset_property C) Y)))) :=
  make_nat_trans _ _ _ (is_nat_trans_yon_comm_w_binprod PC X Y).

Definition yon_comm_w_binprod_inv_nat_trans_data {C : category} (PC : BinProducts C) (X Y : C) :
  nat_trans_data (pr1 (BinProductObject [C^op, HSET, has_homsets_HSET]
                                        (BinProducts_PreShv (yoneda C (homset_property C) X) (yoneda C (homset_property C) Y))))
                 (pr1 (yoneda C (homset_property C) (BinProductObject C (PC X Y)))).
Proof.
  intros Z [f1 f2].
  exact (BinProductArrow _ (PC X Y) f1 f2).
Defined.

Lemma is_nat_trans_yon_comm_w_binprod_inv {C : category} (PC : BinProducts C) (X Y : C) :
  is_nat_trans _ _ (yon_comm_w_binprod_inv_nat_trans_data PC X Y).
Proof.
  unfold yon_comm_w_binprod_inv_nat_trans_data.
  intros Z W f.
  use funextfun; intros [g1 g2]; cbn.
  use BinProductArrowsEq.
  - rewrite (BinProductPr1Commutes _ _ _ _ _ _ _).
    rewrite <- (assoc _ (BinProductArrow _ _ _ _) (BinProductPr1 _ _)).
    rewrite (BinProductPr1Commutes _ _ _ _ _ _ _).
    apply idpath.
  - rewrite (BinProductPr2Commutes _ _ _ _ _ _ _).
    rewrite <- (assoc _ (BinProductArrow _ _ _ _) (BinProductPr2 _ _)).
    rewrite (BinProductPr2Commutes _ _ _ _ _ _ _).
    apply idpath.
Qed.

Definition yon_comm_w_binprod_inv_nat_trans {C : category} (PC : BinProducts C) (X Y : C) :
  nat_trans (pr1 (BinProductObject [C^op, HSET, has_homsets_HSET]
                 (BinProducts_PreShv (yoneda C (homset_property C) X) (yoneda C (homset_property C) Y))))
            (pr1 (yoneda C (homset_property C) (BinProductObject C (PC X Y)))) :=
  make_nat_trans _ _ _ (is_nat_trans_yon_comm_w_binprod_inv PC X Y).

Lemma yon_comm_w_binprod_is_iso {C : category} (PC : BinProducts C) (X Y : C) :
  @is_iso [C^op, HSET, has_homsets_HSET] _ _ (yon_comm_w_binprod_nat_trans PC X Y).
Proof.
  use is_iso_from_is_z_iso.
  exists (yon_comm_w_binprod_inv_nat_trans PC X Y).
  (* unfold yon_comm_w_binprod_nat_trans. *)
  apply tpair.
  - apply (nat_trans_eq has_homsets_HSET); intro Z.
    use funextfun; intro f; cbn.
    unfold yon_comm_w_binprod_nat_trans_data.
    unfold yon_comm_w_binprod_inv_nat_trans_data.
    rewrite <- (BinProductArrowEta _ _ _ _ _ _).
    apply idpath.
  - use (nat_trans_eq has_homsets_HSET); intro Z.
    use funextfun; intro f.
    use dirprodeq; cbn;
    unfold yon_comm_w_binprod_inv_nat_trans_data;
    [use BinProductPr1Commutes | use BinProductPr2Commutes].
Qed.

Lemma yon_comm_w_binprod {C : category} (PC : BinProducts C) :
  ∏ (X Y : C),
  iso (yoneda _ (homset_property _) (BinProductObject _ (PC X Y)))
      (BinProductObject (PreShv _) (BinProducts_PreShv (yoneda _ (homset_property _) X) (yoneda _ (homset_property _) Y))).
Proof.
  intros X Y.
  use make_iso.
  - use yon_comm_w_binprod_nat_trans.
  - use yon_comm_w_binprod_is_iso.
Defined.

(* The isomorphisms between sets. *)

Lemma first_iso (F : cubical_sets) (X : cube_category) :
  iso (pr1 (exp_I F) X) (make_hSet (cubical_sets ⟦y X, exp_I F⟧) (cubical_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use invweq.
  use yoneda_weq.
Defined.

Lemma second_iso (F : cubical_sets) (X : cube_category) :
  @iso HSET
       (make_hSet (cubical_sets ⟦y X, exp_I F⟧) (cubical_homsets _ _))
       (make_hSet (cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧) (cubical_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use invweq.
  use adjunction_hom_weq.
  exact (pr2 (cubical_sets_exponentials I)).
Defined.

Lemma third_iso (F : cubical_sets) (X : cube_category) :
  @iso HSET
       (make_hSet (cubical_sets ⟦constprod_functor1 cubical_sets_binproduct I (y X), F⟧) (cubical_homsets _ _))
       (make_hSet (cubical_sets ⟦y (constprod_functor1 cube_category_binproduct 0 X), F⟧) (cubical_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use iso_comp_right_weq.
  use yon_comm_w_binprod.
Defined.

Lemma fourth_iso (F : cubical_sets) (X : cube_category) :
  @iso HSET
       (make_hSet (cubical_sets ⟦y (constprod_functor1 cube_category_binproduct 0 X), F⟧) (cubical_homsets _ _))
       (pr1 (precomp_functor F) X).
Proof.
  use hset_equiv_iso.
  use yoneda_weq.
Defined.

(* The contravariant homfunctor. (Will be useful.) (Only found bivariant homfunctor in library.) *)

Definition conv_hom_funct_data {C : category} (c : C) : functor_data C^op SET.
Proof.
  use make_functor_data.
  - intro d.
    exact (make_hSet (C ⟦d, c⟧) ((homset_property C) _ _)).
  - intros d d' f g.
    exact ((f : C ⟦d', d⟧) · (g : C ⟦d, c⟧)).
Defined.

Lemma is_functor_conv_hom_funct {C : category} (c : C) : is_functor (conv_hom_funct_data c).
Proof.
  split.
  - intro d.
    apply funextsec; intro x.
    use id_left.
  - intros a b d f g.
    apply funextsec; intro x.
    use assoc'.
Defined.

Definition conv_hom_funct {C : category} (c : C) : functor C^op SET :=
  make_functor _ (is_functor_conv_hom_funct c).

(* The covariant hom-functor. *)

Definition cov_hom_funct_data {C : category} (c : C) : functor_data C SET.
Proof.
  use make_functor_data.
  - intro d.
    exact (make_hSet (C ⟦c, d⟧) ((homset_property C) _ _)).
  - intros d d' f g.
    exact ((g : C ⟦c, d⟧) · (f : C ⟦d, d'⟧)).
Defined.

Lemma is_functor_cov_hom_funct {C : category} (c : C) : is_functor (cov_hom_funct_data c).
Proof.
  split.
  - intro d.
    apply funextsec; intro x.
    use id_right.
  - intros a b d f g.
    apply funextsec; intro x.
    use assoc.
Defined.

Definition cov_hom_funct {C : category} (c : C) : functor C SET :=
  make_functor _ (is_functor_cov_hom_funct c).

(* The isomorphism functors. *)

Definition Fun1_functor_data : functor_data cubical_sets cubical_sets.
Proof.
  use make_functor_data.
  - intro F.
    use functor_composite.
    + exact cubical_sets^op.
    + use functor_opp.
      exact y.
    + exact (conv_hom_funct (exp_I F)).
  - intros F G α.
    use make_nat_trans.
    + intros X f.
      exact (f · (# exp_I α)).
    + intros X Y f.
      use funextsec; intro h.
      use assoc'.
Defined.

Lemma is_functor_Fun1 : is_functor Fun1_functor_data.
Proof.
  split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ set (idax := id_right f);
      rewrite <- (functor_id exp_I F) in idax;
      use idax
    | set (compax := assoc f (# exp_I α) (# exp_I β));
      rewrite <- (functor_comp exp_I α β) in compax;
      use compax ].
Defined.

Definition Fun1 : functor cubical_sets cubical_sets :=
  make_functor _ is_functor_Fun1.

Definition Fun2_functor_data : functor_data cubical_sets cubical_sets.
Proof.
  use make_functor_data.
    - intro F.
      use functor_composite.
      + exact cubical_sets^op.
      + use functor_opp.
        use functor_composite.
        -- exact cubical_sets.
        -- exact y.
        -- exact (constprod_functor1 cubical_sets_binproduct I).
      + exact (conv_hom_funct F).
    - intros F G α.
      use make_nat_trans.
      + intros X f.
        exact (f · α).
      + intros X Y f.
        use funextsec; intro g.
        use assoc'.
Defined.

Lemma is_functor_Fun2 : is_functor Fun2_functor_data.
Proof.
  split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ use id_right | use assoc ].
Defined.

Definition Fun2 : functor cubical_sets cubical_sets :=
  make_functor _ is_functor_Fun2.

Definition Fun3_functor_data : functor_data cubical_sets cubical_sets.
Proof.
  use make_functor_data.
  - intro F.
    use functor_composite.
    + exact cubical_sets^op.
    + use functor_opp.
      use functor_composite.
      * exact cube_category.
      * exact (constprod_functor1 cube_category_binproduct 0).
      * exact y.
    + exact (conv_hom_funct F).
  - intros F G α.
    use make_nat_trans.
    + intros X f.
      exact (f · α).
    + intros X Y f.
      use funextsec; intro g.
      use assoc'.
Defined.

Lemma is_functor_Fun3 : is_functor Fun3_functor_data.
Proof.
   split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ use id_right | use assoc ].
Defined.

Definition Fun3 : functor cubical_sets cubical_sets :=
  make_functor _ is_functor_Fun3.

(* Construction of iso from pointwise iso on two levels. *)

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

(* The isomorphisms on functor level. *)

Lemma first_iso_lv2_nat_trans (F : cubical_sets) :
  is_nat_trans _ (pr1 (Fun1 F)) (λ x, first_iso F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros ?.
  apply (nat_trans_eq has_homsets_HSET); intros a.
  apply funextsec; intros ?.
  apply (maponpaths (pr1 g a)).
  apply pathsdirprod; [|apply idpath].
  now apply funextsec; intro b; cbn; induction (f b).
Time Qed. (* 0.923s *)

Lemma first_iso_lv1_nat_trans :
  is_nat_trans exp_I Fun1
    (λ X, make_nat_trans _ (pr1 (Fun1 X)) (first_iso X) (first_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply (nat_trans_eq has_homsets_HSET); intros a.
  apply funextsec; intros ?.
  apply (maponpaths (pr1 f a)), (maponpaths (pr1 g a)).
  apply pathsdirprod; [|apply idpath].
  now apply funextsec; intros b; cbn; induction (h b).
Time Qed. (* 1.422s *)

Lemma first_functor_iso : @iso [cubical_sets, cubical_sets] exp_I Fun1.
Proof.
  use iso_from_two_lv_iso.
  - use first_iso.
  - use first_iso_lv2_nat_trans.
  - use first_iso_lv1_nat_trans.
Defined.

Lemma second_iso_lv2_nat_trans (F : cubical_sets) :
  is_nat_trans (pr1 (Fun1 F)) (pr1 (Fun2 F)) (λ x, second_iso F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros ?.
  apply maponpaths; apply idpath.
Qed.

Lemma second_iso_lv1_nat_trans :
  is_nat_trans Fun1 Fun2
    (λ X, make_nat_trans (pr1 (Fun1 X)) (pr1 (Fun2 X)) (second_iso X) (second_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply maponpaths; apply idpath.
Time Qed. (* 0.378s *)

Lemma second_functor_iso : @iso [cubical_sets, cubical_sets] Fun1 Fun2.
Proof.
  use iso_from_two_lv_iso.
  - use second_iso.
  - use second_iso_lv2_nat_trans.
  - use second_iso_lv1_nat_trans.
Defined.

Lemma third_iso_lv2_nat_trans (F : cubical_sets) :
  is_nat_trans (pr1 (Fun2 F)) (pr1 (Fun3 F)) (λ x, third_iso F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros x.
  apply funextsec; intros y.
  apply (maponpaths (pr1 g x)), pathsdirprod.
  - apply funextsec; intros [n hn0].
    induction (negnatlthn0 n hn0).
  - apply funextsec; intro n; cbn.
    set (n' := make_stn _ _ _).
    assert (h : n = n').
    { apply subtypePath; [ intros ?; apply propproperty|].
      exact (!(natminuseqn (pr1 n))). }
    rewrite <- h.
    now induction (f n).
Qed.

Lemma third_iso_lv1_nat_trans :
  is_nat_trans Fun2 Fun3
    (λ X, make_nat_trans (pr1 (Fun2 X)) (pr1 (Fun3 X)) (third_iso X) (third_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply maponpaths; apply idpath.
Time Qed. (* 0.041s *)

Lemma third_functor_iso : @iso [cubical_sets, cubical_sets] Fun2 Fun3.
Proof.
  use iso_from_two_lv_iso.
  - use third_iso.
  - use third_iso_lv2_nat_trans.
  - use third_iso_lv1_nat_trans.
Defined.

Lemma fourth_iso_lv2_nat_trans (F : cubical_sets) :
  is_nat_trans (pr1 (Fun3 F)) _ (λ x, fourth_iso F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  set (x := BinProduct_of_functors_mor _ _ cube_category_binproduct
              (constant_functor _ cube_precategory 0)
(functor_identity _) Y X f).
  eapply pathscomp0; [|apply (eqtohomot (nat_trans_ax g _ _ x) (λ i :
⟦ X ⟧, inl i))].
  apply (maponpaths (pr1 g Y)).
  apply funextsec; intros y; cbn.
  set (n' := make_stn _ _ _).
  now induction (f n').
Qed.

Lemma fourth_iso_lv1_nat_trans :
  is_nat_trans Fun3 precomp_functor
    (λ X, make_nat_trans (pr1 (Fun3 X)) _ (fourth_iso X) (fourth_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply idpath.
Qed.

Lemma fourth_functor_iso : @iso [cubical_sets, cubical_sets] Fun3 precomp_functor.
Proof.
  use iso_from_two_lv_iso.
  - use fourth_iso.
  - use fourth_iso_lv2_nat_trans.
  - use fourth_iso_lv1_nat_trans.
Defined.

(* The exponential functor and the precomposition functor are isomorphic. *)

Lemma exp_I_iso_precomp_functor : @iso [[cube_category^op, SET], [cube_category^op, SET]]  precomp_functor exp_I.
Proof.
  use iso_inv_from_iso.
  use (iso_comp first_functor_iso).
  use (iso_comp second_functor_iso).
  use (iso_comp third_functor_iso).
  use fourth_functor_iso.
Defined.

(* The exponential functor has a right adjoint, i.e. the unit interval is tiny. *)

Theorem I_is_tiny : is_left_adjoint exp_I.
Proof.
  use is_left_adjoint_iso.
  - exact cubical_homsets.
  - exact precomp_functor.
  - exact exp_I_iso_precomp_functor.
  - exact precomp_functor_has_right_adjoint.
Defined.



------------------------------------------------------------------------------------------------------



(* We try to generalize the above and find out what properties a category C must have in order for (some) interval object to have a right adjoint. *)

Section generalization.

  Context {C : category}.
  Variable PC : BinProducts C.
  Variable i : C.

Definition preC := PreShv C.

Definition gen_prod_functor : functor C C
  := constprod_functor1 PC i.

Open Scope cat.

(* Definition C_PreShv : category := PreShv C. *)

Definition gen_precomp_functor : functor preC preC.
Proof.
  use pre_composition_functor.
  - apply has_homsets_opp, homset_property.
  - apply functor_opp.
    exact gen_prod_functor.
Defined.

Lemma gen_precomp_functor_has_right_adjoint : is_left_adjoint gen_precomp_functor.
Proof.
  apply RightKanExtension_from_limits.
  apply LimsHSET.
Defined.

Definition yo : C ⟶ preC :=
  yoneda C (homset_property C).

Definition II : preC := yo i.

Definition PreShv_binproduct : BinProducts preC := BinProducts_PreShv.

Definition PreShv_exponentials : Exponentials PreShv_binproduct.
Proof.
  use Exponentials_functor_HSET.
  use has_homsets_opp.
  apply homset_property.
Defined.

Definition exp_II : functor preC preC := pr1 (PreShv_exponentials II).

Definition PreShv_homsets : has_homsets preC := homset_property preC.

(* Naturality of the yoneda isomorphism in [C^op, SET]. *)

Definition eval_functor_data (c : C) : functor_data preC SET.
Proof.
  use make_functor_data.
  - intro F.
    exact (pr1 F c).
  - intros F G α.
    exact (pr1 α c).
Defined.

Lemma is_functor_eval_functor (c : C) : is_functor (eval_functor_data c).
Proof.
  split.
  - intro F.
    apply idpath.
  - intros F G H α β.
    apply idpath.
Defined.

Definition eval_functor (c : C) : functor preC SET :=
  make_functor _ (is_functor_eval_functor c).

Definition cov_comp_w_yo (c : C) : functor preC SET :=
  cov_hom_funct (yo c).

Lemma is_natural_in_preshv_yoneda (c : C) :
  is_nat_trans (cov_comp_w_yo c) (eval_functor c)
               (λ F, yoneda_map_1 C (homset_property C) c F).
Proof.
  intros F G η.
  use funextsec; intro ϕ.
  apply idpath.
Defined.

(* The isomorphisms between sets. *)

Lemma gen_first_iso (F : preC) (X : C) :
  @iso HSET (make_hSet (preC ⟦yo X, exp_II F⟧) (PreShv_homsets _ _)) (pr1 (exp_II F) X).
Proof.
  use hset_equiv_iso.
  use yoneda_weq.
Defined.

Lemma gen_second_iso (F : preC) (X : C) :
  @iso HSET
       (make_hSet (preC ⟦yo X, exp_II F⟧) (PreShv_homsets _ _))
       (make_hSet (preC ⟦constprod_functor1 PreShv_binproduct II (yo X), F⟧) (PreShv_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use invweq.
  use adjunction_hom_weq.
  exact (pr2 (PreShv_exponentials II)).
Defined.

Lemma gen_third_iso (F : preC) (X : C) :
  @iso HSET
       (make_hSet (preC ⟦constprod_functor1 PreShv_binproduct II (yo X), F⟧) (PreShv_homsets _ _))
       (make_hSet (preC ⟦yo (constprod_functor1 PC i X), F⟧) (PreShv_homsets _ _)).
Proof.
  use hset_equiv_iso.
  use iso_comp_right_weq.
  use yon_comm_w_binprod.
Defined.

Lemma gen_fourth_iso (F : preC) (X : C) :
  @iso HSET
       (make_hSet (preC ⟦yo (constprod_functor1 PC i X), F⟧) (PreShv_homsets _ _))
       (pr1 (gen_precomp_functor F) X).
Proof.
  use hset_equiv_iso.
  use yoneda_weq.
Defined.

(* The isomorphism functors. *)

Definition gen_Fun1_functor_data : functor_data preC preC.
Proof.
  use make_functor_data.
  - intro F.
    use functor_composite.
    + exact preC^op.
    + use functor_opp.
      exact yo.
    + exact (conv_hom_funct (exp_II F)).
  - intros F G α.
    use make_nat_trans.
    + intros X f.
      exact (f · (# exp_II α)).
    + intros X Y f.
      use funextsec; intro h.
      use assoc'.
Defined.

Lemma gen_is_functor_Fun1 : is_functor gen_Fun1_functor_data.
Proof.
  split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ set (idax := id_right f);
      rewrite <- (functor_id exp_II F) in idax;
      use idax
    | set (compax := assoc f (# exp_II α) (# exp_II β));
      rewrite <- (functor_comp exp_II α β) in compax;
      use compax ].
Defined.

Definition gen_Fun1 : functor preC preC :=
  make_functor _ gen_is_functor_Fun1.

Definition gen_Fun2_functor_data : functor_data preC preC.
Proof.
  use make_functor_data.
    - intro F.
      use functor_composite.
      + exact preC^op.
      + use functor_opp.
        use functor_composite.
        -- exact preC.
        -- exact yo.
        -- exact (constprod_functor1 PreShv_binproduct II).
      + exact (conv_hom_funct F).
    - intros F G α.
      use make_nat_trans.
      + intros X f.
        exact (f · α).
      + intros X Y f.
        use funextsec; intro g.
        use assoc'.
Defined.

Lemma gen_is_functor_Fun2 : is_functor gen_Fun2_functor_data.
Proof.
  split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ use id_right | use assoc ].
Defined.

Definition gen_Fun2 : functor preC preC :=
  make_functor _ gen_is_functor_Fun2.

Definition gen_Fun3_functor_data : functor_data preC preC.
Proof.
  use make_functor_data.
  - intro F.
    use functor_composite.
    + exact preC^op.
    + use functor_opp.
      use functor_composite.
      * exact C.
      * exact (constprod_functor1 PC i).
      * exact yo.
    + exact (conv_hom_funct F).
  - intros F G α.
    use make_nat_trans.
    + intros X f.
      exact (f · α).
    + intros X Y f.
      use funextsec; intro g.
      use assoc'.
Defined.

Lemma gen_is_functor_Fun3 : is_functor gen_Fun3_functor_data.
Proof.
   split;
    [ intro F | intros F G H α β ];
    use (nat_trans_eq has_homsets_HSET); intro X;
    use funextsec; intro f;
    [ use id_right | use assoc ].
Defined.

Definition gen_Fun3 : functor preC preC :=
  make_functor _ gen_is_functor_Fun3.

(* The isomorphisms on the functor level. *)

Lemma gen_first_iso_lv2_nat_trans (F : preC) :
  is_nat_trans (pr1 (gen_Fun1 F)) _ (λ x, gen_first_iso F x).
Proof.
  use is_natural_yoneda_iso.
Qed.

Lemma gen_first_iso_lv1_nat_trans :
  is_nat_trans gen_Fun1 exp_II
    (λ F, make_nat_trans (pr1 (gen_Fun1 F)) _ (gen_first_iso F) (gen_first_iso_lv2_nat_trans F)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros x.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros y.
  now apply funextsec.
Qed.

Lemma gen_first_functor_iso : @iso [preC, preC] exp_II gen_Fun1.
Proof.
  use iso_inv_from_iso.
  use iso_from_two_lv_iso.
  - use gen_first_iso.
  - use gen_first_iso_lv2_nat_trans.
  - use gen_first_iso_lv1_nat_trans.
Defined.

Lemma gen_second_iso_lv2_nat_trans (F : preC) :
  is_nat_trans (pr1 (gen_Fun1 F)) (pr1 (gen_Fun2 F)) (λ x, gen_second_iso F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros ?.
  apply maponpaths; apply idpath.
Qed.

Lemma gen_second_iso_lv1_nat_trans :
  is_nat_trans gen_Fun1 gen_Fun2
    (λ X, make_nat_trans (pr1 (gen_Fun1 X)) (pr1 (gen_Fun2 X)) (gen_second_iso X) (gen_second_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply (maponpaths (pr1 f x0)).
  apply (maponpaths (pr1 (pr1 g x0 (pr2 h)) x0)).
  now apply pathsdirprod; [use id_left|].
Qed.

Lemma gen_second_functor_iso : @iso [preC, preC] gen_Fun1 gen_Fun2.
Proof.
  use iso_from_two_lv_iso.
  - use gen_second_iso.
  - use gen_second_iso_lv2_nat_trans.
  - use gen_second_iso_lv1_nat_trans.
Defined.

Lemma gen_third_iso_lv2_nat_trans (F : preC) :
  is_nat_trans (pr1 (gen_Fun2 F)) (pr1 (gen_Fun3 F)) (λ x, gen_third_iso F x).
Proof.
  intros X Y f.
  apply funextsec; intro g.
  apply (nat_trans_eq has_homsets_HSET); intros x.
  apply funextsec; intros y.
  apply (maponpaths (pr1 g x)), pathsdirprod; cbn;
  unfold yoneda_morphisms_data, BinProduct_of_functors_mor; cbn.
  - rewrite <- assoc.
    set (foo := BinProductOfArrowsPr1 C (PC i X) (PC i Y) (identity i) f).
    apply maponpaths.
    apply pathsinv0.
    etrans.
    + apply BinProductOfArrowsPr1.
    + now rewrite id_right.
  - apply pathsinv0.
    rewrite <- assoc.
    etrans.
    + eapply maponpaths.
      apply BinProductOfArrowsPr2.
    + apply assoc.
Qed.

Lemma gen_third_iso_lv1_nat_trans :
  is_nat_trans gen_Fun2 gen_Fun3
    (λ X, make_nat_trans (pr1 (gen_Fun2 X)) (pr1 (gen_Fun3 X)) (gen_third_iso X) (gen_third_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros h.
  apply maponpaths; apply idpath.
Time Qed. (* 0.041s *)

Lemma gen_third_functor_iso : @iso [preC, preC] gen_Fun2 gen_Fun3.
Proof.
  use iso_from_two_lv_iso.
  - use gen_third_iso.
  - use gen_third_iso_lv2_nat_trans.
  - use gen_third_iso_lv1_nat_trans.
Defined.

Lemma gen_fourth_iso_lv2_nat_trans (F : preC) :
  is_nat_trans (pr1 (gen_Fun3 F)) _ (λ x, gen_fourth_iso F x).
Proof.
  intros X Y f.
  use (is_natural_yoneda_iso _ _ _ _ _ (BinProduct_of_functors_mor _ _ PC _ _ _ _ _)).
Qed.

Lemma gen_fourth_iso_lv1_nat_trans :
  is_nat_trans gen_Fun3 gen_precomp_functor
    (λ X, make_nat_trans (pr1 (gen_Fun3 X)) _ (gen_fourth_iso X) (gen_fourth_iso_lv2_nat_trans X)).
Proof.
  intros X Y f.
  apply (nat_trans_eq has_homsets_HSET); intros ?.
  apply funextsec; intros g.
  apply idpath.
Qed.

Lemma gen_fourth_functor_iso : @iso [preC, preC] gen_Fun3 gen_precomp_functor.
Proof.
  use iso_from_two_lv_iso.
  - use gen_fourth_iso.
  - use gen_fourth_iso_lv2_nat_trans.
  - use gen_fourth_iso_lv1_nat_trans.
Defined.

(* The exponential functor and the precomposition functor are isomorphic. *)

Lemma gen_exp_I_iso_precomp_functor : @iso [preC, preC]  gen_precomp_functor exp_II.
Proof.
  use iso_inv_from_iso.
  use (iso_comp gen_first_functor_iso).
  use (iso_comp gen_second_functor_iso).
  use (iso_comp gen_third_functor_iso).
  use gen_fourth_functor_iso.
Defined.

(* The exponential functor has a right adjoint, i.e. the unit interval is tiny. *)

Theorem gen_I_is_tiny : is_left_adjoint exp_II.
Proof.
  use is_left_adjoint_iso.
  - exact PreShv_homsets.
  - exact gen_precomp_functor.
  - exact gen_exp_I_iso_precomp_functor.
  - exact gen_precomp_functor_has_right_adjoint.
Defined.
