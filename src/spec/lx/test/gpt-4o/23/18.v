Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec " This striThis is a long string that has many characters in itng has a 
 newline character" 90.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.