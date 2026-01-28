Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_BBrownLazyLazy : strlen_spec "BBrownLazyLazy  " 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.