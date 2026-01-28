Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_unicode : strlen_spec "àèìòùáéíóúýâêîôûãñõäëïöàèìòùáiséíóúýâêîôûãñõäëïöüÿçüÿç" 106.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.