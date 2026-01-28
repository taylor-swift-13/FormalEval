Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Tish!whyNcJH1whyLaàèìòùáéíóúùýâê   

  1s  îôãñõäëïöüÿçQFoQxukyickytothe  	 H1th  4" 109.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.