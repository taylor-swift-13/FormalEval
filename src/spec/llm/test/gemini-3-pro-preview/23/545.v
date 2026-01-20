Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["yyy"], output = 3 *)
Example test_strlen_yyy : strlen_spec "yyy" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.