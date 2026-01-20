Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = [" This striThis is a long string that has many characters in itng has a \n newline character"], output = 90 *)
Example test_strlen_complex : strlen_spec (" This striThis is a long string that has many characters in itng has a " ++ String (ascii_of_nat 10) " newline character") 90.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.