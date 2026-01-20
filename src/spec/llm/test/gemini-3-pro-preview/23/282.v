Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["why1NcJH1th"], output = 11 *)
Example test_strlen_why1NcJH1th : strlen_spec "why1NcJH1th" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.