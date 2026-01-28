Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "MNhqThe CQuick Brown hFox Jumps OveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpskgmCV" 152.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.