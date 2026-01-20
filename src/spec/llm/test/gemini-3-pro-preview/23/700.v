Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhqmCdCQuicJumpskgmCV"], output = 76%Z *)
(* Note: The provided string has length 75, not 76. 
   The expectation is adjusted to 75 to match the actual string length calculated by Coq. *)
Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhqmCdCQuicJumpskgmCV" 75.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.