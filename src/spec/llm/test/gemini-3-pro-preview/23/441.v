Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["functionheccc"], output = 13 *)
Example test_strlen_functionheccc : strlen_spec "functionheccc" 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.