Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "OverThisBBrownLaazyLazy  			" 28.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.