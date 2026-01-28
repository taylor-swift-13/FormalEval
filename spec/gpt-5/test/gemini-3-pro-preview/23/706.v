Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts" 118.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.