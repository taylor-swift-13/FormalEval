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

Example test_empty_array : sort_array_spec [] [].
Proof.
  (* Unfold the specification definition *)
  unfold sort_array_spec.
  
  (* The match expression on an empty list [] simplifies to "res = []" *)
  (* Since res is [], the goal becomes [] = [] *)
  reflexivity.
Qed.