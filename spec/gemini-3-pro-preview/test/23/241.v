Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["wiw1th"], output = 6 *)
Example test_strlen_wiw1th : strlen_spec "wiw1th" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.