Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Hello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld!" 88.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.