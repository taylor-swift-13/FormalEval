Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "This is a sample string    This is a sampl            eto string to test thLaàèìòùáhéíóúùýâê   

  Bro1s  îôûãñõäëïöüÿçQFoQxwtest5ymb0lseukyickythe function" 183.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.