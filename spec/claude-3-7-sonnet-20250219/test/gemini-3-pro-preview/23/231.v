Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "The QuiisJumpsck Brown Fox Jg" 29.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.