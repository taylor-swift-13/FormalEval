Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "stCQuicMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVstrOveringumpskt" 80.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.