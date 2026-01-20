Require Import Coq.Arith.Arith.

Definition sum_to_n_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_25 :
  sum_to_n_spec 25 325.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.