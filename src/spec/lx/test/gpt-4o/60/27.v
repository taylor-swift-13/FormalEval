Require Import Coq.Arith.Arith.

Definition sum_to_n_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_21 :
  sum_to_n_spec 21 231.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.