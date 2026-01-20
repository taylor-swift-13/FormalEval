Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "BrownLazMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sastr1str1ngnsgmple string to test th e functionCdV The BrownLazy DogmCVys" 132.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.