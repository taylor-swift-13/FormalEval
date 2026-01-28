Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "àèìòùáéíóúýâêîôiwTish!!1thûãñõäëïöüÿçtnwtest5ymb0lscQukiwhyLLaàèìòùáéíóúùýâê   

  1s  îôûãñõäëïöüÿçQFoQxukyickytothe  	 H1thkn
Brown" 186.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.