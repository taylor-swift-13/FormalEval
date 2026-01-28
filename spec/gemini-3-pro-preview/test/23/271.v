Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["fux      ncc"], output = 12 *)
Example test_strlen_1 : strlen_spec "fux      ncc" 12.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.