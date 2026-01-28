Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["st1r1n"], output = 6 *)
Example test_strlen_st1r1n : strlen_spec "st1r1n" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.