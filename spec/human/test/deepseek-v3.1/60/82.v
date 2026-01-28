Require Import ZArith.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output : nat) : Prop :=
  2 * output = n * (n + 1).

Example test_case_1 : problem_60_spec 39 780.
Proof.
  unfold problem_60_spec.
  simpl.
  compute. (* Or you can also use lia. *)
  lia.
Qed.