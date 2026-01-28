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

Example test_sort_array : sort_array_spec [30; 20; 10; 5] [5; 10; 20; 30].
Proof.
  unfold sort_array_spec.
  simpl.
  split.
  - transitivity (5 :: [30; 20; 10]).
    + apply Permutation_sym.
      apply Permutation_cons_app with (l1 := [30; 20; 10]) (l2 := []).
      reflexivity.
    + constructor.
      transitivity (10 :: [30; 20]).
      * apply Permutation_sym.
        apply Permutation_cons_app with (l1 := [30; 20]) (l2 := []).
        reflexivity.
      * constructor.
        apply perm_swap.
  - repeat constructor; red; simpl; discriminate.
Qed.