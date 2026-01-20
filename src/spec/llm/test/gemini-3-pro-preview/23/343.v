Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["   \nhyN cJH\n  string"], output = 20 *)
(* Note: Although the prompt mentions 20%Z, the specification defines res as nat, 
   so we use the natural number 20 to ensure type correctness. *)
Example test_strlen_multiline : strlen_spec "   
hyN cJH
  string" 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.