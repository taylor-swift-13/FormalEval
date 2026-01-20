Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Th!s 1s w1This is a sample sstrintog ton test the functiont4 str1str1ngng w1th 5ymb0ls !n 1t" 92.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.