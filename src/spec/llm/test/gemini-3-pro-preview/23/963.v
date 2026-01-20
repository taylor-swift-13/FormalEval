Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["aLLaa zz aaick"], output = 14 *)
(* Note: Although the prompt mentions 14%Z, the specification defines res as nat, 
   so we use the natural number 14 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "aLLaa zz aaick" 14.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.