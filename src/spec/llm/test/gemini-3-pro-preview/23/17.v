Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["three\nfour\nfive"], output = 15 *)
Example test_strlen_multiline : strlen_spec "three
four
five" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.