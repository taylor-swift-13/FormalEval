Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThBrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCLazyk BrowMNhqmn Fox Jumps OverThis  to ytehst t" 116.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.