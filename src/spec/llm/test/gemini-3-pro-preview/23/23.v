Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["11234567890"], output = 11 *)
(* Note: Although the prompt mentions 11%Z, the specification defines res as nat, 
   so we use the natural number 11 to ensure type correctness. *)
Example test_strlen_numeric_string : strlen_spec "11234567890" 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.