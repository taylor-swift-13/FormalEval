Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "why1N  p  This is a sampleto string to test the function          cJH1th" 72.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.