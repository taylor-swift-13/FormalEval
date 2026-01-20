Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "Th!s 1s 4 str1ng w1th 5ymb0ls !n 1testMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVt1tt Over The TBrowMNhqmnrownisgmCV" 130.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.