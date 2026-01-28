Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "whyNcJH11thîôûãñõäëïöüÿçQFoQxwtest5ymb0lseukyickythefunnc" 70.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.