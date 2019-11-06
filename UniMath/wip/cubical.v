(** Cartesian Cube Category *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.MoreFoundations.Propositions.

(* Konstruktion med FiniteSet *)

Definition cube_precategory_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor FiniteSet (λ (I J : FiniteSet), J → (I ⨿ (stnset 2))). (* Vad är bäst, ⟦2⟧ eller bool? *)

Definition cube_precategory_data : precategory_data.
Proof.
  exists cube_precategory_ob_mor.
  split.
  - intro I.
    exact (λ (i : pr1 I), inl i).
  - intros I J K f g k.
    induction (g k).
    + exact (f a).
    + exact (inr b).
Defined.

Definition cube_precategory : precategory.
Proof.
  exists cube_precategory_data.
  apply make_is_precategory_one_assoc.
  - intros I J f.
    apply funextfun.
    intro j.
    cbn.
    now induction (f j).
  - intros I J g.
    apply idpath.
  - intros I J K L f g h.
    apply funextfun.
    intro l.
    cbn.
    now induction (h l).
Defined.

