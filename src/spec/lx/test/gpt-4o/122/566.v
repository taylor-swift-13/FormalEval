Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition sum_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example sum_test :
  sum_spec [1000000; 200; 3; 40; 5000000; 60; 7; 4999999; 8000; 9; 10; 7; 200] 8 110.
Proof.
  unfold sum_spec.
  simpl.
  reflexivity.
Qed.