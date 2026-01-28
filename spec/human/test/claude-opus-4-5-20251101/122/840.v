Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition is_at_most_two_digits (n : Z) : bool :=
  (Z.ltb (-100) n) && (Z.ltb n 100).

Definition problem_122_pre (arr : list Z) (k : nat) : Prop :=
  (length arr >= 1)%nat /\ (length arr <= 100)%nat /\ (1 <= k)%nat /\ (k <= length arr)%nat.

Definition problem_122_spec (arr : list Z) (k : nat) (result : Z) : Prop :=
  let first_k_elements := firstn k arr in
  let filtered_elements := filter is_at_most_two_digits first_k_elements in
  result = fold_left Z.add filtered_elements 0.

Example test_problem_122 :
  problem_122_spec [-99%Z; -88%Z; -77%Z; -66%Z; -55%Z; -33%Z; -22%Z; -11%Z; 3030%Z; 11%Z; 22%Z; 33%Z; 44%Z; 55%Z; 66%Z; 77%Z; 88%Z; 99%Z] 9%nat (-451%Z).
Proof.
  unfold problem_122_spec.
  simpl.
  reflexivity.
Qed.