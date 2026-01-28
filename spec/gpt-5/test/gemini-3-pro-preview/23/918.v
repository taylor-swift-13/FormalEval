Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "Th!s 1s 4 str1ng w1th 5ymb0ls !nw 1testt1tt Over The TBrowMNhqmnrownisgmCV" 74.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.