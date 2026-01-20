Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "one
twota
thrThis is a long string that has many characters ien itee
four
five" 78.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.