Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "BrownLazMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test th e functionCdV The BrownLazy DogmCVys" 119.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.