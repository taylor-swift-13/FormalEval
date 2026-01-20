Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "Th    This iTh!s 1s RL4 str1ng wtest5ymb0l !n 1t
s a sample TTetnstrinisg Jumpet   

wtest5ymb40ls    t
" 104.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.