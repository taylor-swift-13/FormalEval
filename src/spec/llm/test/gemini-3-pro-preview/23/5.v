Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["12345"], output = 5 *)
Example test_strlen_12345 : strlen_spec "12345" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.