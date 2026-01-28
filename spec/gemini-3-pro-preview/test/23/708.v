Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe CQuicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV"], output = 88 *)
Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV" 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.