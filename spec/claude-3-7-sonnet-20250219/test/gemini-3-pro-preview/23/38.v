Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "thrieeThe quick brown fox jumps overq the lazy dog
four
five" 60.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.