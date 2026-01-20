Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "whyLaàèìòùáéíóúùýâê   

  1s  îôãñõäëïöüÿçQFoQxukyickytothe  	 H1th" 93.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.