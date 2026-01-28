Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCV" 77.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.