Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "GThT    1t 1 The CuQuicJumpsk   ic" 34.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.