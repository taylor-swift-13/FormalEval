Require Import Coq.Arith.Arith.

Definition sum_to_n_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example sum_to_n_test_1 :
  sum_to_n_spec 210 22155.
Proof.
  unfold sum_to_n_spec.
  replace (2 * 22155) with 44310 by reflexivity.
  replace (210 * (210 + 1)) with 44310 by reflexivity.
  reflexivity.
Qed.