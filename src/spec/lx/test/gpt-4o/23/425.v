Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_special_chars :
  Spec "Th!s 1s RL4 str1ng wtest5ymb0l !n 1t
" 37.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.