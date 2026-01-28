Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_long : strlen_spec "The quick brown fox jumps over the lazy This striThis is a long string that has many characters in itng has a 
 newline character dog" 133.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.