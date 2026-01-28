Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Tis"], output = 3 *)
Example test_strlen_Tis : strlen_spec "Tis" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.