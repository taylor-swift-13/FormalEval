Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_ps1ss :
  Spec "ps1ss" 5.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.