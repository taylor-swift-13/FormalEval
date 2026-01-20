Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLaLazy z zyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts" 125.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.