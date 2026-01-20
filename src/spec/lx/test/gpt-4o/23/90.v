Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "one
twotaa
thrThis is a long string that has many characters ien itee
1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5four
five" 175.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.