Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuick Brown Fox oJumps Over The BrownLazy DogmCV" 57.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.