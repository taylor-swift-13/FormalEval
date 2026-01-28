Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLaLazy z zyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1tsrrstr1ng" 133.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.