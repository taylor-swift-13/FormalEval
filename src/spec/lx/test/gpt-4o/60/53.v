Require Import Coq.Arith.Arith.

Definition sum_to_n_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_88 :
  sum_to_n_spec 88 3916.
Proof.
  unfold sum_to_n_spec.
  simpl.
  reflexivity.
Qed.