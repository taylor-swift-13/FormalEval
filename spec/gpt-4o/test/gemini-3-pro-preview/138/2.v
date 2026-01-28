Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_6 : ~ is_equal_to_sum_even_spec 6.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge Heven].
  unfold ge in Hge.
  repeat apply le_S_n in Hge.
  inversion Hge.
Qed.