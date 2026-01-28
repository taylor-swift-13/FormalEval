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

Example test_sort_array : sort_array_spec [8; 9; 9; 7; 9] [7; 8; 9; 9; 9].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - apply Permutation_sym.
    change [8; 9; 9; 7; 9] with ([8; 9; 9] ++ 7 :: [9]).
    apply Permutation_cons_app.
    simpl.
    apply Permutation_refl.
  - repeat (constructor; try (unfold Z.le; vm_compute; discriminate)).
Qed.