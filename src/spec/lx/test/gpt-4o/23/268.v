Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_complex :
  Spec " àèìòùáéíóúýâêîôiwTish!1thûãñõäëïöüÿç  

wtest5ymb40ls    " 84.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.