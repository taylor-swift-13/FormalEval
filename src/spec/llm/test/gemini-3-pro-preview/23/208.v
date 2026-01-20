Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["    4\n\n  1s  "], output = 13 *)
Example test_strlen_complex : strlen_spec "    4

  1s  " 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.