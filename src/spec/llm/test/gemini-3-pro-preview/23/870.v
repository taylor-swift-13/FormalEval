Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["CQuticJumpsk"], output = 12 *)
Example test_strlen_CQuticJumpsk : strlen_spec "CQuticJumpsk" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.