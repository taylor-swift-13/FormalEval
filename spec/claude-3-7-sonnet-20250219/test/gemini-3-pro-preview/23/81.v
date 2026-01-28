Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a 
 newline character5rstuvwxyz" 141.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.