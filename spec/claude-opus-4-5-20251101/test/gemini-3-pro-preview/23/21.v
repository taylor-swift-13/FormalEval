Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "The quick brown fox jumps over the lazy This striThis is aaracter dog" 69.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.