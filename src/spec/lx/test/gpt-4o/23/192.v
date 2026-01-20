Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_unicode :
  Spec "     ã         ô àèìòùáéíóúýâêîôûãñõäëïöüÿç  " 73.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.