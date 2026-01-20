Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "Testing te stingone
twot
thrThis is a long string that has many characters in itee
four
five 123" 96.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.