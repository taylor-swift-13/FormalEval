Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "w  CdV  1This is a sample sstrintogt ton test the functiont" 59.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.