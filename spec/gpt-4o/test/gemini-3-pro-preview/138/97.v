Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_110 : is_equal_to_sum_even_spec 110.
Proof.
  unfold is_equal_to_sum_even_spec.
  split.
  - do 8 apply le_n_S. apply Nat.le_0_l.
  - reflexivity.
Qed.