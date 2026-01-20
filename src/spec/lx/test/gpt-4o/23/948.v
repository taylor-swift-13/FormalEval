Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_brownlazuey :
  Spec "BrownLazuey" 11.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.