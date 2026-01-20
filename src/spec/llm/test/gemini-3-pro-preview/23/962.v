Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["testtt"], output = 6 *)
(* Note: Although the prompt mentions 6%Z, the specification defines res as nat, 
   so we use the natural number 6 to ensure type correctness. *)
Example test_strlen_testtt : strlen_spec "testtt" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.