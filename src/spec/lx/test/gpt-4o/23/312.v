Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "    This is a sample TTetnstrinisg tiiiso test the function           " 70.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.