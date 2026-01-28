Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.

Definition problem_60_pre (n : nat) : Prop := n > 0.

Definition problem_60_spec (n output: nat) : Prop :=
  2 * output = n * (n + 1).

Example problem_60_example_1 :
  problem_60_spec 89 4005.
Proof.
  unfold problem_60_spec.
  simpl.
  lia.
Qed.