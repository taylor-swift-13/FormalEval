Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_complex : strlen_spec "thrieeThe quick brown fox jumps overq the lazy dog
four
five" 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.