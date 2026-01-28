Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["isJumps"], output = 7 *)
Example test_strlen_isJumps : strlen_spec "isJumps" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.