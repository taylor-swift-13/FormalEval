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
  problem_122_spec [111; 1111; 22; 222; 333; 445; 555; 777; 888; 999; 1000; 2000; 8000; 4040; -78; 5050; 6000; 7000; 8000; 9000] 12 22.
Proof.
  unfold problem_122_spec.
  simpl firstn.
  simpl filter.
  simpl fold_left.
  reflexivity.
Qed.