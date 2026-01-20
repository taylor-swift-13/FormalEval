Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "Hello, WoG1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick by Thisthree
four
fiveracter dogQyadEborlod!" 197.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.