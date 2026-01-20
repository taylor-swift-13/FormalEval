Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["The quick brown fox jumps over the lazy This striThis is aaracter dog"], output = 69 *)
Example test_strlen_long : strlen_spec "The quick brown fox jumps over the lazy This striThis is aaracter dog" 69.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.