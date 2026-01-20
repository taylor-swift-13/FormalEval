Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "one
twot
thrThis is a long string that has  many characterns in itee
four
five" 78.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.