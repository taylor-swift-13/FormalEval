Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \n\n  "], output = 7 *)
(* Note: Although the prompt mentions 7%Z, the specification defines res as nat, 
   so we use the natural number 7 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "   

  " 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.