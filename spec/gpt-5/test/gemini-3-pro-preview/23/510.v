Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "wtest5ymb0lscQukiwhyLaàèìòùáéíóúùýâê   

  1s  îôûãñõäëïöüÿçQFoQxukyickytothe  	 H1thkn" 114.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.