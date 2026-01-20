Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_of_foive :
  Spec "of foive" 8.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.