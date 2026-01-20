Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition is_equal_to_sum_even_spec (n : nat) : Prop :=
  n >= 8 /\ Nat.even n = true.

Example test_case_input_4 : ~ is_equal_to_sum_even_spec 4.
Proof.
  unfold is_equal_to_sum_even_spec.
  intros [H_ge H_even].
  (* H_ge states that 4 >= 8, which is equivalent to 8 <= 4. This is false. *)
  lia.
Qed.