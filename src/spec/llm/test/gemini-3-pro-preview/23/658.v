Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["     str1ng 1t  The    This is a sampleOvering to test the function"], output = 67 *)
Example test_strlen_long_string : strlen_spec "     str1ng 1t  The    This is a sampleOvering to test the function" 67.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.