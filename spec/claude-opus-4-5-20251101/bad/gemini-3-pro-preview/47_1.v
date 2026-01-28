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

Example test_median : median_spec [3; 1; 2; 4; 5] 3.
Proof.
  unfold median_spec. split.
  - intro H. inversion H.
  - exists [1; 2; 3; 4; 5].
    split.
    + (* Prove Permutation *)
      apply Permutation_trans with (l' := [1; 3; 2; 4; 5]).
      * apply perm_swap.
      * apply perm_skip.
        apply Permutation_trans with (l' := [2; 3; 4; 5]).
        -- apply perm_swap.
        -- apply Permutation_refl.
    + split.
      * (* Prove is_sorted *)
        unfold is_sorted. intros i j [Hlt Hlen].
        simpl in Hlen.
        (* We use repeated destruct to handle the finite cases of indices i and j *)
        destruct i; [| destruct i; [| destruct i; [| destruct i; [| destruct i; [| lia ]]]]];
        destruct j; [| destruct j; [| destruct j; [| destruct j; [| destruct j; [| lia ]]]]];
        (* Verify sorted condition for all cases, discarding invalid ones with lia *)
        simpl; try lra; try lia.
      * split.
        -- (* Prove length equality *)
           reflexivity.
        -- (* Prove median result *)
           left. split.
           ++ reflexivity.
           ++ simpl. reflexivity.
Qed.