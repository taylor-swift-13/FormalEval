Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "Th!s 1s 4 str1n0g wtest5ymb0lse !n 1t
" 38.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.