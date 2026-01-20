Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNe CQuick Brown Fox oJumps Over The BrownLazy DogmCV" 53.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.