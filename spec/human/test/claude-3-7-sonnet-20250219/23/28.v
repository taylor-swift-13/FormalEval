Require Import String.
Require Import Coq.Strings.String.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec(input : string) (output : nat) : Prop :=
  output = length input.

Example test_strlen_long_string :
  problem_23_spec "one
twot
thrThis is a long string thtat has many characters in itee
four
five" 77.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.