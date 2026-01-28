Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition problem_122_pre (arr : list Z) (k : nat) : Prop :=
  (1 <= Z.of_nat (length arr) <= 100)%Z /\ (1 <= Z.of_nat k <= Z.of_nat (length arr))%Z.

Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example test_case_correct :
  problem_122_spec [201; -88; -78; -66; -55; -44; -33; -22; -11; 0; 11; 22; 34; 44; 55; 66; 77; 88; 99] 9 (-397).
Proof.
  unfold problem_122_spec.
  simpl firstn.
  simpl filter.
  simpl fold_left.
  reflexivity.
Qed.