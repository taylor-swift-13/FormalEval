Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_fox : strlen_spec "The quick brown fox jumps over the lazy dog" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.