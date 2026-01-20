Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "    This is a sample strintg to test the function          " 59.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.