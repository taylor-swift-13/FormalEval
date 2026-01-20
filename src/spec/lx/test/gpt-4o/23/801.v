Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "to   Thihs is a sa
mple string to test the function

   z" 57.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.