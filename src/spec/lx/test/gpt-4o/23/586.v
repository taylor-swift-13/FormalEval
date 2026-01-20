Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCV" 55.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.