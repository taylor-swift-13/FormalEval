Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["hyNJcJ"], output = 6 *)
Example test_strlen_hyNJcJ : strlen_spec "hyNJcJ" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.