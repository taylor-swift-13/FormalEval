Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "Laàèìòùáéíóúùýâê   

  1s  îôûãñõäëïöüÿçQFoQxukyicky" 79.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.