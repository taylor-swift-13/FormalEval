Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a 
 newline character5rstuvwxyz"], output = 141 *)
Example test_strlen_complex : strlen_spec "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a 
 newline character5rstuvwxyz" 141.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.