Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintoTh!s 1s 4 str1ng w1th 5ymb0ls !n 1testMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVt1tt Over The TBrowMNhqmnrownisgmCVg to test the functiongmCV" 236.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.