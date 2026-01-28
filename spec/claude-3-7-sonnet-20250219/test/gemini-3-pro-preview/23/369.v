Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Th    This is a sample TTetnstrinisg Jumpeto test the function           !s40ls !n 1t
" 86.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.