Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "ThT Th!s 1s 4 sstr1str1ngng w1th 5ymb0ls !n 1t   1t 1 The    i" 62.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.