Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_symbols :
  Spec "Th!s 1s 4 str1ng wtest5ymb40ls s!n 1t
" 38.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.