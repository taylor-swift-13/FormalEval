Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_54 : is_equal_to_sum_even_spec 54.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - unfold ge. repeat constructor.
  - reflexivity.
Qed.