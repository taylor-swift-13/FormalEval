Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_107 : ~ is_equal_to_sum_even_spec 107.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [_ Heven].
  simpl in Heven.
  discriminate Heven.
Qed.