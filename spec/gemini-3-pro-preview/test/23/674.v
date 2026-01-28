Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DogmCV"], output = 57 *)
Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DogmCV" 57.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.