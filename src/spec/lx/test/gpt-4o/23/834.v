Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "BBrownLLazyLazy  " 17.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.