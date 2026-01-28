Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example test_case_122 :
  problem_122_spec [90; 80; 70; 60; 50; 40; 30; 90; 70] 3 240.
Proof.
  unfold problem_122_spec.
  simpl.
  unfold is_at_most_two_digits.
  simpl.
  reflexivity.
Qed.