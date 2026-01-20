Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Testing testingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 95.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.