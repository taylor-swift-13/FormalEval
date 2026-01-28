Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["one..."], output = 175 *)
Example test_strlen_complex : strlen_spec "one
twotaa
thrThis is a long string that has many characters ien itee
1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5four
five" 175.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.