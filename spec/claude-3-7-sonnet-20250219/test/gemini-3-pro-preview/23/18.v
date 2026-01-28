Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec " This striThis is a long string that has many characters in itng has a 
 newline character" 90.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.