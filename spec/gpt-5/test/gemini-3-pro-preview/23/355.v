Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "whyLaàèìòùáéíóúùýâê   

  1s  îôãñõäëïöüÿçQFoQxukyickytothe  	 H1th" 93.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.