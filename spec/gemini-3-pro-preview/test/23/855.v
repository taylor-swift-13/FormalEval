Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["DogmC    \n\n func!ntion  Lazyk"], output = 29 *)
(* Note: Although the prompt mentions 29%Z, the specification defines res as nat, 
   so we use the natural number 29 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "DogmC    

 func!ntion  Lazyk" 29.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.