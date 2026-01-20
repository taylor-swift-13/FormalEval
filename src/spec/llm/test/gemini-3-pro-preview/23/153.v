Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["    This is a sampl           eto string to test the func tion          "], output = 72 *)
Example test_strlen_complex : strlen_spec "    This is a sampl           eto string to test the func tion          " 72.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.