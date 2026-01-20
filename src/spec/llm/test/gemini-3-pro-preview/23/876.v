Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["    samThT "], output = 11 *)
Example test_strlen_complex : strlen_spec "    samThT " 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.