Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps over the lazy This striThis is aaracter dog" 69.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.