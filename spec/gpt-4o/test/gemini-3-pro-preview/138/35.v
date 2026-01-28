Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_57 : ~ is_equal_to_sum_even_spec 57.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [_ H].
  simpl in H.
  discriminate.
Qed.