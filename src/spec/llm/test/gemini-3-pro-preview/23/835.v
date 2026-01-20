Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["stCQuicMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVstrOveringumpskt"], output = 80 *)
Example test_strlen_complex : strlen_spec "stCQuicMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVstrOveringumpskt" 80.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.