Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_symbols :
  Spec "Th!s 1s 4 sstr1str1ngng w1th 5ymb0ls !n 1t" 42.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.