Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazy" 66.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.