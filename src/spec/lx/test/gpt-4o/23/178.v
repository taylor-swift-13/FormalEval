Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_special_chars :
  Spec "Th!s40ls !n 1t
" 15.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.