Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCV" 59.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.