Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "oMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test thCV" 77.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.