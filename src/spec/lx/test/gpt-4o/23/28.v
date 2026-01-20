Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "one
twot
thrThis is a long string thtat has many characters in itee
four
five" 77.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.