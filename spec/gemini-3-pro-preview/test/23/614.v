Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \n\n   z"], output = 9 *)
(* Note: Although the prompt mentions 9%Z, the specification defines res as nat, 
   so we use the natural number 9 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "   

   z" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.