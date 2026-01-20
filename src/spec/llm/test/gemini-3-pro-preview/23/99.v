Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "one
twota
thrThis is a long string that has many characters iThe quick bis striThis is aaracter dogMen itee
four
five" 117.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.