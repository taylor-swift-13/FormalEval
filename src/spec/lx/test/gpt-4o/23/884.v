Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe Quick Brown Fox Jumps Over The BrownLazy DogmCrV" 56.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.