Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "  Th!s 1s 4 st1r1ng wtest5nymb0ls !nsampleto 1t
" 48.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.