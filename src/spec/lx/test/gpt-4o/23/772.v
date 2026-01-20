Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "Th!s 1s 4 str1ng w1thTTBrownis    55ymb0ls !n 1t" 48.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.