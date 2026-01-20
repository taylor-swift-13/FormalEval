Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "ThT OverThisBBrownLaazyLazy   t1t 1 The    i" 44.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.