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

Example test_sort_array : sort_array_spec [0; 1; 11; 0; 0; 0] [11; 1; 0; 0; 0; 0].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply perm_trans with (l' := [0; 11; 1; 0; 0; 0]).
    + apply perm_skip. apply perm_swap.
    + apply perm_trans with (l' := [11; 0; 1; 0; 0; 0]).
      * apply perm_swap.
      * apply perm_skip. apply perm_swap.
  - repeat constructor; unfold Z.ge; vm_compute; discriminate.
Qed.