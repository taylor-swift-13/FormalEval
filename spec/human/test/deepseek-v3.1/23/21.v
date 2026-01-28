Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_strlen_non_empty : problem_23_spec "The quick brown fox jumps over the lazy This striThis is aaracter dog" 69.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.