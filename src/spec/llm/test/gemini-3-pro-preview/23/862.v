Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Th!s 1s 4Cr1ngng w1th 5ymb0ls !n 1t"], output = 35 *)
(* Note: Although the prompt mentions 35%Z, the specification defines res as nat, 
   so we use the natural number 35 to ensure type correctness. *)
Example test_strlen_complex : strlen_spec "Th!s 1s 4Cr1ngng w1th 5ymb0ls !n 1t" 35.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.