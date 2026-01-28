Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["MNhqThe Quick Brown FoxJumps Over The BrownLazy DogmCV"], output = 54 *)
(* Note: Although the prompt mentions 54%Z, the specification defines res as nat, 
   so we use the natural number 54 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "MNhqThe Quick Brown FoxJumps Over The BrownLazy DogmCV" 54.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.