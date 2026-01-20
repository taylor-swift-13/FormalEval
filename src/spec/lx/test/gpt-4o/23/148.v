Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "Fo    This is a sampleto string to test the function  n        x" 64.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.