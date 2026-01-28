Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_newline :
  problem_23_spec "GNDThis string has a 
 newline characterdEb" 43.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.