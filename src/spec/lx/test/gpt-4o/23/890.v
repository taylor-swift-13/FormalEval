Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "GThT    1t 1 The CuQuicJumpsk   ic" 34.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.