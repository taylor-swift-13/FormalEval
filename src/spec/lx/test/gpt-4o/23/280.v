Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "  Th!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
" 46.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.