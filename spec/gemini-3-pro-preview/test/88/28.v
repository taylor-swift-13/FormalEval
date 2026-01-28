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

Example test_sort_array_custom : 
  sort_array_spec 
    [3; 1; 9; 2; 8; 3; 7; 4; 6; 5] 
    [9; 8; 7; 6; 5; 4; 3; 3; 2; 1].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply Permutation_cons_app with (l1 := [9; 8; 7; 6; 5; 4]) (l2 := [3; 2; 1]). simpl.
    apply Permutation_cons_app with (l1 := [9; 8; 7; 6; 5; 4; 3; 2]) (l2 := []). simpl.
    apply Permutation_cons_app with (l1 := []) (l2 := [8; 7; 6; 5; 4; 3; 2]). simpl.
    apply Permutation_cons_app with (l1 := [8; 7; 6; 5; 4; 3]) (l2 := []). simpl.
    apply Permutation_cons_app with (l1 := []) (l2 := [7; 6; 5; 4; 3]). simpl.
    apply Permutation_cons_app with (l1 := [7; 6; 5; 4]) (l2 := []). simpl.
    apply Permutation_cons_app with (l1 := []) (l2 := [6; 5; 4]). simpl.
    apply Permutation_cons_app with (l1 := [6; 5]) (l2 := []). simpl.
    apply Permutation_cons_app with (l1 := []) (l2 := [5]). simpl.
    apply Permutation_cons_app with (l1 := []) (l2 := []). simpl.
    constructor.
  - repeat (constructor; simpl; try discriminate).
Qed.