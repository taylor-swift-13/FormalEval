Require Import Coq.Arith.Arith.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_4 : ~ is_equal_to_sum_even_spec 4.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [Hge Heven].
  unfold ge in Hge.
  (* The hypothesis Hge is 8 <= 4. We can reduce this to a contradiction. *)
  repeat apply le_S_n in Hge.
  (* Now Hge is 4 <= 0, which is impossible. *)
  inversion Hge.
Qed.