Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["nnshthes"], output = 8 *)
Example test_strlen_nnshthes : strlen_spec "nnshthes" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.