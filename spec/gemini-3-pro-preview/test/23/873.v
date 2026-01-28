Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["C"], output = 1 *)
Example test_strlen_C : strlen_spec "C" 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.