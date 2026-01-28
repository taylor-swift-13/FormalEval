Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["1234 This sitriThis is a long string that has many characters in itng has a \n newline character5"], output = 96 *)
Example test_strlen_long : strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5" 96.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.