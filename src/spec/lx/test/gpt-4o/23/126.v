Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample_string :
  Spec "    This is a sampleto string to test the function          " 60.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.