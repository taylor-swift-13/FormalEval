Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "Th    This is a sample TTetnstrinisg Jumpeto test the function           !s40ls !n 1t
" 86.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.