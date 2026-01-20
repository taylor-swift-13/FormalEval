Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "thThT OaverThisBBrownLaazyLazye   t1t 1 The    iCVeLBrownLazazy" 63.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.