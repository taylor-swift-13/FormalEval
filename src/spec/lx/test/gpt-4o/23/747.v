Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "to   This is a sample string to test the function

   z" 55.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.