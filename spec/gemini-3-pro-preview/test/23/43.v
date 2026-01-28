Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = [" This striThis is a long string that has many characters in itng has a 
 neawline character"], output = 91 *)
Example test_strlen_complex : strlen_spec " This striThis is a long string that has many characters in itng has a 
 neawline character" 91.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.