Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogQyadEb" 219.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.