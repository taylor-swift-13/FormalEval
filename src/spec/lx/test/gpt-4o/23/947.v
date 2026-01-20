Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "Th!s 1s 4s str1str1ngng w1th 5ymb0ls !n 1tBrow" 46.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.