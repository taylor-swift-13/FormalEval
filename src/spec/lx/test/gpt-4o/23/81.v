Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a 
 newline character5rstuvwxyz" 141.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.