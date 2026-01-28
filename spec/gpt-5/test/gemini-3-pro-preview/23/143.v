Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_utf8 : strlen_spec " ã          àèìòùáéíóúýâêîôûãñõäëïöüÿç" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.