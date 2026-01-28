Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_1 : strlen_spec "Th    This is a sample TTetnstrinisg to test the function           !s40ls !n 1t
" 81.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.