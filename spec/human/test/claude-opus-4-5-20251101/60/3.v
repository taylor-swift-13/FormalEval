Require Import Nat.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_sum_to_n_11 : problem_60_spec 11 66.
Proof.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.