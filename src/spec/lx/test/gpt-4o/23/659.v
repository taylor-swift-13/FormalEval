Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Th!s 1s 4 str1str1ngng w1th 5ymb0ls !n 1tBrownLazys" 51.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.