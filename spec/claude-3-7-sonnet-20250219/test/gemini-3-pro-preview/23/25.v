Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_sentence : strlen_spec "The quick brown f ox jumps over the lazy dog" 44.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.