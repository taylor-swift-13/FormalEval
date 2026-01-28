Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "àèìòùáéíóúýâêîôiwTish!!1thûãñõäëïöüÿçtnwtest5ymb0lscQukiwhyLLaàèìòùáéíóúùýâê   

  1s  îôûãñõäëïöüÿçQFoQxukyickytothe  	 H1thkn
Brown" 186.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.