Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "whyLaàèìòùáéíóúùýâê   

  1s  îôûãñõäëïöüÿçQFoQxukyickytothe  	 H1th" 95.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.