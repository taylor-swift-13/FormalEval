Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["GNDThis string has a \n newline characterdEb"], output = 43 *)
(* Note: Although the prompt mentions 43%Z, the specification defines res as nat, 
   so we use the natural number 43 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "GNDThis string has a 
 newline characterdEb" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.