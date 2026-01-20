Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKQyadEb" 106.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.