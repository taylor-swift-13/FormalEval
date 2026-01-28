Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Dëàèìòùõäëïÿçgog" 28.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.