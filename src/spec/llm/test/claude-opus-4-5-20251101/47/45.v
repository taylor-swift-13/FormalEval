Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.Reals.Reals.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Lra.
Import ListNotations.

Open Scope R_scope.

Definition is_sorted (l : list R) : Prop :=
  forall i j, (i < j < length l)%nat -> nth i l 0 <= nth j l 0.

Definition median_spec (l : list R) (result : R) : Prop :=
  l <> [] /\
  exists sorted_l : list R,
    Permutation l sorted_l /\
    is_sorted sorted_l /\
    length sorted_l = length l /\
    ((Nat.odd (length l) = true /\
      result = nth (length l / 2) sorted_l 0) \/
     (Nat.even (length l) = true /\
      result = (nth (length l / 2 - 1) sorted_l 0 + nth (length l / 2) sorted_l 0) / 2)).

Definition IZR_list (l : list Z) : list R := map IZR l.

Example median_test : median_spec (IZR_list [1%Z; 1%Z; 1%Z; 4%Z; 9%Z; 1%Z]) 1.0%R.
Proof.
  unfold median_spec.
  split.
  - unfold IZR_list. simpl. discriminate.
  - exists (IZR_list [1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 9%Z]).
    split.
    + unfold IZR_list. simpl.
      apply perm_trans with (IZR 1 :: IZR 1 :: IZR 1 :: IZR 4 :: IZR 9 :: IZR 1 :: nil).
      * apply Permutation_refl.
      * apply perm_trans with (IZR 1 :: IZR 1 :: IZR 1 :: IZR 4 :: IZR 1 :: IZR 9 :: nil).
        -- apply perm_skip. apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap.
        -- apply perm_trans with (IZR 1 :: IZR 1 :: IZR 1 :: IZR 1 :: IZR 4 :: IZR 9 :: nil).
           ++ apply perm_skip. apply perm_skip. apply perm_skip. apply perm_swap.
           ++ apply Permutation_refl.
    + split.
      * unfold is_sorted, IZR_list. simpl.
        intros i j [Hij Hj].
        destruct i as [|[|[|[|[|[|i']]]]]];
        destruct j as [|[|[|[|[|[|j']]]]]];
        simpl; try lia; try lra.
      * split.
        -- unfold IZR_list. simpl. reflexivity.
        -- right. split.
           ++ simpl. reflexivity.
           ++ unfold IZR_list. simpl. lra.
Qed.