Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe Quick Brown FoxJumps Over The BrownLazy DogmCV" 54.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.