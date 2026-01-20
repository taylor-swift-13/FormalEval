Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_wtest5ymb0l :
  Spec "wtest5ymb0l" 11.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.