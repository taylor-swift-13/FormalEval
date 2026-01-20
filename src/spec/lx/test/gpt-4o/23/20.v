Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "1234 This striThis is a long string that has many characters in itng has a 
 newline character5" 95.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.