Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_special :
  Spec "Th!s 1s 4 stTheTer1ng wtest5ymb0lse !n 1t
" 42.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.