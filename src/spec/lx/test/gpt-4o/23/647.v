Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_nonempty :
  Spec "BrowMNhqThe CQuick Brown Fstrintogwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazy" 87.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.