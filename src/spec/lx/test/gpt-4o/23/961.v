Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec " Th!s 1s 4 str1ng w1thn 5ymb0ls !n 1t Over The TTBrownisgmCV" 60.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.