Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "Th    This is a sample TTetnstrinisg to test the function           !s40ls !n 1t
" 81.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.