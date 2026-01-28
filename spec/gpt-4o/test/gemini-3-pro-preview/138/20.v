Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_21 : ~ is_equal_to_sum_even_spec 21.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge Heven].
  simpl in Heven.
  discriminate.
Qed.