Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "This is a sample string    This is a sampl            eto string to test thLaàèìòùáéíóúùýâê   

  Bro1s  îôûãñõäëïöüÿçQFoQxukyickythe function" 169.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.