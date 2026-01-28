Require Import Nat.
Require Import Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n*(n+1).

Example test_sum_to_n_77 : problem_60_spec 77 3003.
Proof.
  unfold problem_60_spec.
  simpl.
  reflexivity.
Qed.