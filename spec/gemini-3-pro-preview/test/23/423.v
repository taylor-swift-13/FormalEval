Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input with special characters and newlines *)
(* The string contains multi-byte characters (UTF-8). Coq's String.length counts bytes. *)
(* Calculated length is 85 bytes, which differs from the character count 59. *)
Example test_strlen_complex : strlen_spec " àèìòùáéíóúýâêîôiwTish!!1thûãñõäëïöüÿç  

wtest5ymb40ls    " 85.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.