Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["	"], output = 1 *)
Example test_strlen_tab : strlen_spec "	" 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.