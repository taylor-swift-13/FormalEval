Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "MNhqThe CQuicJumpsk BBrownLazyLazyBrown Fox Jumps  OverThis is a sample string to test thCV" 91.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.