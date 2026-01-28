Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_long :
  problem_23_spec (" This striThis is a long string that has many characters in itng has a \n newline character") 90.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.