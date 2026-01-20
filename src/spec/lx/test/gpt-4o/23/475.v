Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "Tish!whyNcJH1whyLaàèìòùáéíóúùýâê   

  1s  îôãñõäëïöüÿçQFoQxukyickytothe  	 H1th  4" 109.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.