Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_symbols :
  Spec "Th!s 1s str1ng wtest5ymb0ls !n 1t
" 34.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.