Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "   ThiBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazys is a sample string to test th e function

   z" 120.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.