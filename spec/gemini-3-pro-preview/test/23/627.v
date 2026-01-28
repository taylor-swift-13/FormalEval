Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["GThT    1t 1 The    ic"], output = 22 *)
Example test_strlen_complex : strlen_spec "GThT    1t 1 The    ic" 22.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.