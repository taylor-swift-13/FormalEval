Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_BBrownLazyLazy : strlen_spec "BBrownLazyLazy  " 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.