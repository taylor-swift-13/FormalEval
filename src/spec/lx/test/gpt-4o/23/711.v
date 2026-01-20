Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNhqThe CQuDogmCVnsampBrownleLazyick Brown Fox oJutesttmps Oqver The BrownLazy DogmCV" 85.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.