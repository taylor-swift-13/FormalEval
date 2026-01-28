Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test thCV"], output = 76 *)
Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test thCV" 76.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.