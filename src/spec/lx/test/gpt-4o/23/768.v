Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuick Brown hFox Jumps OveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpsk
gmCV" 153.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.