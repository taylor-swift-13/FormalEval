Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long :
  Spec "MNhqThe Quick BrowTBrowMNhqmnrownisgmCVgn FoxJumpws Over The BrownLazy DogmCV" 77.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.