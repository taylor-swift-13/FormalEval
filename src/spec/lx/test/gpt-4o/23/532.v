Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_special_chars :
  Spec " àèìòùáéíóúýâêîôiwTish!!1th1ûãñõäëïöüÿç  

wtest5ymb40ls    " 86.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.