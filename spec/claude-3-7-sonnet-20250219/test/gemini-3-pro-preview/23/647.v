Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "BrowMNhqThe CQuick Brown Fstrintogwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazy" 87.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.