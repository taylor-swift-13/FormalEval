Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "This is a sample strintog to tesMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCVt the function" 151.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.