Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_funthec :
  Spec "funthec" 7.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.