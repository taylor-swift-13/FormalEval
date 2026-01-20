Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec "Th!s 1s 4 sTtTheTer1ng wtest5ymb0lse !n 1t
Jum5ymb0lsmfunct ion" 63.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.