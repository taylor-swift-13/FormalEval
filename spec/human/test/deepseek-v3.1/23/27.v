Require Import String.
Require Import ZArith.

Definition problem_23_pre (input : string) : Prop := True.

Definition problem_23_spec (input : string) (output : nat) : Prop :=
  output = String.length input.

Example test_strlen_long : problem_23_spec "Testing testingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 95.
Proof.
  unfold problem_23_spec.
  reflexivity.
Qed.