Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "Hello, WoG1234 This sitriThis is a long string that has many characters in itng h as a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazby Thisthree
four
fiveracter dogQyadEborlod!" 236.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.