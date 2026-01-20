Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown hFox Jumps OveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpskgmCV" 152.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.