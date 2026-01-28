Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps over theThe quick brown fox jxumps overq the lazy dog lazy Thisthree
four
fiveracter dog" 114.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.