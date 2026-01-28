Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_multiline :
  problem_23_spec "one
two
three
four
five" 23.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.