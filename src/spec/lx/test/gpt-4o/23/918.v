Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "Th!s 1s 4 str1ng w1th 5ymb0ls !nw 1testt1tt Over The TBrowMNhqmnrownisgmCV" 74.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.