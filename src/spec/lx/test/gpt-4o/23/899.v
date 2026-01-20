Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "BrowMNhqThe CQuick Brown Fstrintogwox Jumpes Over The BrownLazuey DogmCVnsampBrownleLazy" 88.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.