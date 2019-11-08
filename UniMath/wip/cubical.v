(** Proof that the interval in cartesian cubical sets is tiny *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.CategoryTheory.limits.binproducts.

(* Construction oc cartesian cube category using nat as object set *)

Definition cube_precategory_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor nat (λ (m n : nat), (stnset n) → (stnset m ⨿ stnset 2)).

Definition cube_precategory_data : precategory_data.
Proof.
  exists cube_precategory_ob_mor.
  split.
  - intro n.
    exact (λ (i : stnset n), inl i).
  - intros l m n f g i.
    induction (g i).
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

Open Scope stn.

Definition combined_fun {X : UU} (m n : nat) (f : stnset m → X) (g : stnset n → X) : stnset (m + n) → X.
Proof.
  intro a.
  set (i := pr1 a).
  set (b := natgtb m i).
  apply bool_rect.
  - set (make_stn m i b).

Definition cube_category_binproduct : BinProducts cube_category.
Proof.
  intros m n.
  use make_BinProduct.
  - exact (m + n).
  - exact (λ (i : stnset m), inl ((stn_left m n) i)).
  - exact (λ (i : stnset n), inl ((stn_right m n) i)).
  - use make_isBinProduct.
    + exact (pr2 cube_category).
    + intros l f g.
      unfold iscontr.
      use tpair.
      * use tpair.
        -- intro i.
           set (j := pr1 i).
           set (b := natgtb m j).
           Check ● j.
           exact (if b then f (j ,, b) else g (n j )).