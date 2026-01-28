Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen : strlen_spec "The quick brown fox11234567890 jumps over the lazy This striThis is aaracter dog" 80.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.