Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["sTh!s4strinisg05ymb0lsls"], output = 24 *)
Example test_strlen_complex : strlen_spec "sTh!s4strinisg05ymb0lsls" 24.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.