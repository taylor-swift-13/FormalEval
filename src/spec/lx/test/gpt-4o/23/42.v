Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "one twot This striThis is a long streing that has many characters in itng has a 
 newline character
three
four
five" 115.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.