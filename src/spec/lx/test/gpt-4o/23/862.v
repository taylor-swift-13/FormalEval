Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "Th!s 1s 4Cr1ngng w1th 5ymb0ls !n 1t" 35.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.