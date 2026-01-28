Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "Th!s1s 1s 4 str1ng w1th 5ymb0ls !n 1t" 37.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.