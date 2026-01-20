Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_wtest5ymb40ls :
  Spec "wtest5ymb40ls" 13.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.