Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = [""], output = 0 *)
(* Note: Although the prompt mentions 0%Z, the specification defines res as nat, 
   so we use the natural number 0 to ensure type correctness. *)
Example test_strlen_empty : strlen_spec "" 0.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.