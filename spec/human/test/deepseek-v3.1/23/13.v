Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_strlen_newline : problem_23_spec "This string has a 
 newline character" 37.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.