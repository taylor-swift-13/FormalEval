Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_BBrownLazyLazy :
  Spec "BBrownLazyLazy  " 16.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.