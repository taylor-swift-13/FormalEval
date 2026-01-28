Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["The quick brown f ox jumps over the lazyg"], output = 41%Z *)
Example test_strlen_complex : strlen_spec "The quick brown f ox jumps over the lazyg" 41.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.