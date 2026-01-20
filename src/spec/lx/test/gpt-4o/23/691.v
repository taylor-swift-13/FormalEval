Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "Tihis sample string to      The     test the function" 53.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.