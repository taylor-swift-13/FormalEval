Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" 86.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.