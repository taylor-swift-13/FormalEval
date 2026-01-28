Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["pFomThfGqorZJum5ymb0lsmtopss"], output = 28 *)
Example test_strlen_custom : strlen_spec "pFomThfGqorZJum5ymb0lsmtopss" 28.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.