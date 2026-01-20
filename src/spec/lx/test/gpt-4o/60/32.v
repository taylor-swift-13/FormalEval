Require Import Coq.Arith.Arith.

Definition sum_to_n_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_23 :
  sum_to_n_spec 23 276.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.