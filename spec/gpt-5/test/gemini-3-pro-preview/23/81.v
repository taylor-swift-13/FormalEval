Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a 
 newline character5rstuvwxyz" 141.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.