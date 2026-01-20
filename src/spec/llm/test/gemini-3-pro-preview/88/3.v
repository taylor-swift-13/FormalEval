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

Example test_sort_array : sort_array_spec [2; 4; 3; 0; 1; 5] [0; 1; 2; 3; 4; 5].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply Permutation_trans with (l' := 0 :: [2; 4; 3; 1; 5]).
    + apply Permutation_sym. apply (Permutation_middle [2; 4; 3] [1; 5] 0).
    + apply perm_skip.
      apply Permutation_trans with (l' := 1 :: [2; 4; 3; 5]).
      * apply Permutation_sym. apply (Permutation_middle [2; 4; 3] [5] 1).
      * apply perm_skip.
        apply perm_skip.
        apply perm_swap.
  - repeat constructor; compute; discriminate.
Qed.