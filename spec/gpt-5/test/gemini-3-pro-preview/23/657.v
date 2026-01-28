Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 str1ng w1th 5ymb0ls !n 1t Over The TTBrownisgmCV" 58.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.