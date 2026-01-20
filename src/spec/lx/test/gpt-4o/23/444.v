Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "JTh!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1tum5ymb0lsmfunction" 62.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.