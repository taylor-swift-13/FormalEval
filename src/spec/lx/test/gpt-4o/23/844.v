Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "MNhqThe C Quic   k Brown FTh!s 1s 4 str1ng w1th 5ymb0ls !n 1testMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVt1tt Over The TBrowMNhqmnrownisgmCVox Jumps Over TheC BrownLazy DogmCV" 191.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.