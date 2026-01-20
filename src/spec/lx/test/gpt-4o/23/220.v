Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_symbols :
  Spec "Th!s1s 1s 4 str1ng w1th 5ymb0ls !n 1t" 37.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.