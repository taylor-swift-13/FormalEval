Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Coq.micromega.Lia.
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

Example test_sort_array : sort_array_spec [7; 9; 11; 11] [11; 11; 9; 7].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - replace [11; 11; 9; 7] with (rev [7; 9; 11; 11]) by reflexivity.
    apply Permutation_rev.
  - repeat constructor; try lia.
Qed.