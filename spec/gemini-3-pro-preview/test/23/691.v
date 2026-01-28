Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Tihis sample string to      The     test the function"], output = 53 *)
(* Note: Although the prompt mentions 53%Z, the specification defines res as nat, 
   so we use the natural number 53 to ensure type correctness. *)
Example test_strlen_long : strlen_spec "Tihis sample string to      The     test the function" 53.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.