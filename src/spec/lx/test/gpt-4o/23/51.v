Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKQyadEb" 106.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.