Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a 
 newline character5rstuvwxyz" 141.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.