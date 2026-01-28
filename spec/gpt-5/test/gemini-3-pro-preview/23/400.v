Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_input : strlen_spec "This is a sample string    This is a sampl            eto string to test thLaàèìòùáhéíóúùýâê   

  Bro1s  îôûãñõäëïöüÿçQFoQxwtest5ymb0lseukyickythe function" 183.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.