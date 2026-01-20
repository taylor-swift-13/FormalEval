Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "leOvMNhqThe CQuick Brown Fox oJumps Ovepr The BrownLazy DogmCVering" 67.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.