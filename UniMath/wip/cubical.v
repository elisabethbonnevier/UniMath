(** Proof that the interval in cartesian cubical sets is tiny *)

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.Combinatorics.StandardFiniteSets.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.MoreFoundations.Propositions.
Require Import UniMath.CategoryTheory.limits.binproducts.

Open Scope stn.

(* Construction of cartesian cube category using nat as object set *)

Definition cube_precategory_ob_mor : precategory_ob_mor :=
  make_precategory_ob_mor nat (λ (m n : nat), (stn n) → (stn m ⨿ stn 2)).

Definition cube_precategory_data : precategory_data.
Proof.
  exists cube_precategory_ob_mor.
  split.
  - intro n.
    exact (λ (i : stn n), inl i).
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

Lemma natlth_to_coprod (m n i : nat) : i < m + n → (i < m) ⨿ (i - m < n).
Proof.
  intro p.
  induction (natlthorgeh i m) as [q1 | q2].
  - exact (inl q1).
  - set (p' := (natlehlthtrans m i (m + n)) q2 p).
    set (q3 := natlthandminusl i (m + n) m p p').
    rewrite (natpluscomm m n) in q3.
    rewrite (plusminusnmm n m) in q3.
    exact (inr q3).
Defined.

Definition combined_fun {X : UU} (m n : nat) (f : stn m → X) (g : stn n → X) : stn (m + n) → X.
Proof.
  intro a.
  set (i := pr1 a).
  induction (natlth_to_coprod m n i (pr2 a)) as [H1 | H2].
  - exact (f (make_stn m i H1)).
  - exact (g (make_stn n (i - m) H2)).
Defined.

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
        -- exact (combined_fun m n f g).
        --