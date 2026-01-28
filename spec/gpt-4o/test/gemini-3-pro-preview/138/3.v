Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_8 : is_equal_to_sum_even_spec 8.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - apply le_n.
  - reflexivity.
Qed.