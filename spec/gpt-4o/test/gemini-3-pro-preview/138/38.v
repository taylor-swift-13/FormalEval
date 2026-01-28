Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_0 : ~ is_equal_to_sum_even_spec 0.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge _].
  inversion Hge.
Qed.