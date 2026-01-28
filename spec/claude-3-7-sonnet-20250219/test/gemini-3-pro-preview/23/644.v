Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 sstr1str1ngng w1th 5ymb0ls !n 1t" 42.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.