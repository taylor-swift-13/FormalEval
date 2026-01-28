Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

Example test_strlen_long : strlen_spec "    This  is a sample TTetnstrinisg to test the function           " 67.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.