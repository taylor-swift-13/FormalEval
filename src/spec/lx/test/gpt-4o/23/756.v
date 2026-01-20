Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNhqThe CQuicJumpsk Browno Fox Jumps Over The BrownLazy DogmCV" 62.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.