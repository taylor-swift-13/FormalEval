Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_sentence : strlen_spec "The quick brown fox jumps over the lazy dog" 43.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.