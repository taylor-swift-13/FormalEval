Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Import ListNotations.
Open Scope Z_scope.

Definition sort_array_spec (array : list Z) (res : list Z) : Prop :=
  match array with
  | [] => res = []
  | first :: _ =>
      let last_val := last array first in
      let sum_val := first + last_val in
      Permutation array res /\
      (if Z.odd sum_val 
       then Sorted Z.le res 
       else Sorted Z.ge res)
  end.

Example test_sort_array : sort_array_spec [10%Z; 7%Z; 9%Z; 11%Z; 11%Z; 9%Z] [7%Z; 9%Z; 9%Z; 10%Z; 11%Z; 11%Z].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply perm_trans with (7 :: 10 :: 9 :: 11 :: 11 :: 9 :: []).
    + apply perm_swap.
    + apply perm_skip.
      apply perm_trans with (9 :: 10 :: 11 :: 11 :: 9 :: []).
      * apply perm_swap.
      * apply perm_skip.
        apply perm_trans with (10 :: 11 :: 9 :: 11 :: []).
        { apply perm_skip. apply perm_skip. apply perm_swap. }
        apply perm_trans with (10 :: 9 :: 11 :: 11 :: []).
        { apply perm_skip. apply perm_swap. }
        apply perm_trans with (9 :: 10 :: 11 :: 11 :: []).
        { apply perm_swap. }
        apply perm_skip.
        apply Permutation_refl.
  - repeat (constructor; simpl; try discriminate).
Qed.