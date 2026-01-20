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

Example test_sort_array : sort_array_spec [4; 3; 2; 1] [1; 2; 3; 4].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - assert (H: [4; 3; 2; 1] = rev [1; 2; 3; 4]) by reflexivity.
    rewrite H.
    apply Permutation_sym.
    apply Permutation_rev.
  - repeat (constructor; try (unfold Z.le; compute; discriminate)).
Qed.