Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "stgrsr1ngLqNtCZAtest" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.