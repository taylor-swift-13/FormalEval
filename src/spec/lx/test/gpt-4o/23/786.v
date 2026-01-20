Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "functontMNhqThe CQuDogmCVnsampBrownleLazyick Brown Fox oJutesttmps OqveThT     testt1t 1 The    iMNhq1TMNMNhqTheher The BrownLazy DogmCV" 136.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.