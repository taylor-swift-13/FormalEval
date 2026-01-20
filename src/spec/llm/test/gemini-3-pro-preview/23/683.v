Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["DogmCVown  GThT "], output = 16 *)
(* Note: Although the prompt mentions 16%Z, the specification defines res as nat, 
   so we use the natural number 16 to ensure type correctness. *)
Example test_strlen_custom : strlen_spec "DogmCVown  GThT " 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.