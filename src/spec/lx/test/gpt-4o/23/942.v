Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "Ju   This is a sampleT stringunction

   zTTBrownismbUmvrKpes" 61.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.