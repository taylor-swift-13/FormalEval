Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintoTh!s 1s 4 str1ng w1th 5ymb0ls !n 1testMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVt1tt Over The TBrowMNhqmnrownisgmCVg to test the functiongmCV" 237.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.