Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "GThT    1t 1 The CuQuicJumpsk   ic" 34.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.