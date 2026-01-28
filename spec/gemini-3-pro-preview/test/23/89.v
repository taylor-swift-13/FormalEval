Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec 
  ("one" ++ String (ascii_of_nat 10) ("twot" ++ String (ascii_of_nat 10) ("thrThis is a long string that has  many characterns in itee" ++ String (ascii_of_nat 10) ("four" ++ String (ascii_of_nat 10) "five")))) 
  78.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.