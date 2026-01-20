Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_large :
  Spec " ã          àèòìòùáéíóúýâêîôûãñõäëïöàèìòùáéíóúýâêîôûãñõäëïöüÿçüÿç" 119.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.