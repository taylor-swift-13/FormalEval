Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_strlen_longstring : problem_23_spec "one
twota
thrThis is a long string that has many characters in itee
four
five" 77.
Proof.
  unfold problem_23_spec.
  simpl.
  reflexivity.
Qed.