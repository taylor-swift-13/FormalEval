Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["TTBrownis    "], output = 13 *)
Example test_strlen_1 : strlen_spec "TTBrownis    " 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.