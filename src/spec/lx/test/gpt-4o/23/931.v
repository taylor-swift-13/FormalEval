Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_over_this_bbrown_laazy_lazy :
  Spec "OverThisBBrownLaazyLazy" 23.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.