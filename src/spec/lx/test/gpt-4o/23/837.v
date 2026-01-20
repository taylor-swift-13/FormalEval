Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "CQuDogmCVnsampBrownfunctBwownisLazyLazy" 39.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.