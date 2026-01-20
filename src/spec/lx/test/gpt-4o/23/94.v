Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "1234 This sitriThis is a long string that has many character12345s in itng has a 
 newline character5" 101.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.