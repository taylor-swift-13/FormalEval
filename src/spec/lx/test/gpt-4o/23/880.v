Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test thhe function The BrownLazy DogmCV" 106.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.