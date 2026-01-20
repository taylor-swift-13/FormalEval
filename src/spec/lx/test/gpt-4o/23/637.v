Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazy" 79.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.