Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_unicode : strlen_spec "Dëàèìòù4áéíóúýâêîôûãñõäëïÿçgog" 55.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.