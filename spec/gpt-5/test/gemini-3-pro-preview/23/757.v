Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "BrownsampBrownlMNhqThe CQuicJumpsk BBrownLazyLazyBrown Fox Jumps  OverThis is a sample string to test thCVeLazy" 111.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.