Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_case :
  Spec "MNhqThe CQu			ick Brown func!ntionFox oJutesttmps Over The BrownLazy DogmCV" 75.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.