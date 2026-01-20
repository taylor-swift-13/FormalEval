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

Example test_sort_array : sort_array_spec [1%Z; 9%Z; 2%Z; 8%Z; 3%Z; 7%Z; 4%Z; 6%Z; 5%Z] [9%Z; 8%Z; 7%Z; 6%Z; 5%Z; 4%Z; 3%Z; 2%Z; 1%Z].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply NoDup_Permutation.
    + repeat constructor; simpl; intuition discriminate.
    + repeat constructor; simpl; intuition discriminate.
    + intro x; simpl; intuition.
  - repeat constructor; vm_compute; discriminate.
Qed.