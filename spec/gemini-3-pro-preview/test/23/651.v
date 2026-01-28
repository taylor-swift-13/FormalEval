Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["      1t  The    "], output = 17 *)
Example test_strlen_spaces : strlen_spec "      1t  The    " 17.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.