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

Example test_sort_array : sort_array_spec [1; 2; 3; 1; 1; 2] [1; 1; 1; 2; 2; 3].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply perm_skip.
    transitivity (1 :: [2; 3] ++ [1; 2]).
    + symmetry. apply Permutation_middle.
    + simpl. apply perm_skip.
      transitivity (1 :: [2; 3] ++ [2]).
      * symmetry. apply Permutation_middle.
      * simpl. apply perm_skip.
        apply perm_skip.
        apply perm_swap.
  - repeat constructor; compute; congruence.
Qed.