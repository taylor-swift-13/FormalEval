Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuick Brown Fox Jumps Over The BrownLazy DogmCV" 56.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.