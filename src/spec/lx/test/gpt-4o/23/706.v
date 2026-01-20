Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts" 118.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.