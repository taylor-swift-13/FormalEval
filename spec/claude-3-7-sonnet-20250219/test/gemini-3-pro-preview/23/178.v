Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_1 : strlen_spec "Th!s40ls !n 1t
" 15.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.