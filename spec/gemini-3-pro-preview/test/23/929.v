Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe CQuick Brown hFox Jumps OcveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpskgmCV"], output = 153 *)
(* Note: The original requirement asked for 154, but the actual length of the string is 153. 
   The proof has been corrected to use 153 to satisfy the specification. *)
Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown hFox Jumps OcveMNhqThe CQuicJumpsk Brown Fox Jumps  OverThis is a sample string to test thCVr The BrownLazy DoMNhqmCdCQuicJumpskgmCV" 153.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.