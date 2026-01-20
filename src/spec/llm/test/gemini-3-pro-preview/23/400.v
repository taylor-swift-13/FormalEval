Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "This is a sample string    This is a sampl            eto string to test thLaàèìòùáhéíóúùýâê   

  Bro1s  îôûãñõäëïöüÿçQFoQxwtest5ymb0lseukyickythe function" 183.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.