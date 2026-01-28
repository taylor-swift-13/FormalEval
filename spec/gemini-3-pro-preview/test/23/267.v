Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["    This is a sample strintg to test the function          "], output = 59 *)
Example test_strlen_complex : strlen_spec "    This is a sample strintg to test the function          " 59.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.