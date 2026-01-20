Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["The quick brown fox jumps over the lazy dog"], output = 43 *)
Example test_strlen_sentence : strlen_spec "The quick brown fox jumps over the lazy dog" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.