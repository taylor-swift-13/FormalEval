Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe CQuicJumpsk Brown Fox Jumps Over The BrownLazy DogmCV" 61.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.