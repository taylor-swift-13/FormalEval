Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_strlen_empty : problem_23_spec "" 0.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.