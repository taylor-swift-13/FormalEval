Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "BrownsampBrownlMNhqThe CQuicJumpsk BBrownLazyLazyBrown Fox Jumps  OverThis is a sample string to test thCVeLazy" 111.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.