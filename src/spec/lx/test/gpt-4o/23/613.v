Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_large :
  Spec "MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCV" 105.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.