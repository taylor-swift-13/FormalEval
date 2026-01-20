Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCV
hCV" 63.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.