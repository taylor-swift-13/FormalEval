Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "Th!s 1s 4 str1str1ngng w1th 5ymb0ls !n 1tBrownLazys" 51.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.