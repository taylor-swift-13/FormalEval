Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe CQuick Brown Fox oJutesttmps Oqver The BrownLazy DogmCV" 63.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.