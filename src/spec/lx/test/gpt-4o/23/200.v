Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "   

wwtest5ymb40ls    " 23.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.