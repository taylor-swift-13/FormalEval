Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "leOvMNhqThe CQuick Brown Fox oJumps Over The BrownLazy DogmCVering" 66.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.