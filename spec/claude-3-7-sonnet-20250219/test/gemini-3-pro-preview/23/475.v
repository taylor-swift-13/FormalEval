Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Tish!whyNcJH1whyLaàèìòùáéíóúùýâê   

  1s  îôãñõäëïöüÿçQFoQxukyickytothe  	 H1th  4" 109.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.