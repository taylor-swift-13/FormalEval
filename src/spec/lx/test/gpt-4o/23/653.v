Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_sample :
  Spec "MNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCV" 77.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.