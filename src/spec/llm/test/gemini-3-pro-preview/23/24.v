Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "one
twot
thrThis is a long string that has many characters in itee
four
five" 76.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.