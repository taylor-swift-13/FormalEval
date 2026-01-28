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
  problem_122_spec [111%Z; 799%Z; 22%Z; 222%Z; 333%Z; 300%Z; 444%Z; 555%Z; 666%Z; 777%Z; 888%Z; 999%Z; 1000%Z; 2000%Z; 3030%Z; 5050%Z; 6000%Z; 8000%Z; 9000%Z; 444%Z; 1000%Z; 2000%Z; 2000%Z] 10%nat 22%Z.
Proof.
  unfold problem_122_spec.
  simpl.
  reflexivity.
Qed.