Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["BBBo"], output = 4 *)
Example test_strlen_BBBo : strlen_spec "BBBo" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.