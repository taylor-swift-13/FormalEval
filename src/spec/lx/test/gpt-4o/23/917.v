Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_new :
  Spec "   ThiBrowMNhqThe CQuick FoxJumpsBrown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z" 128.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.