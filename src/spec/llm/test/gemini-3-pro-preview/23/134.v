Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["a"], output = 1 *)
(* Note: Although the prompt mentions 1%Z, the specification defines res as nat, 
   so we use the natural number 1 to ensure type correctness. *)
Example test_strlen_a : strlen_spec "a" 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.