Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "  Th!s 1s 4 st1   

wwtest5ymb40ls    r1ng wtest5nymb0ls !nsampleto 1t
" 71.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.