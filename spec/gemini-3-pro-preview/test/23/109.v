Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["The Quick Brown Fox Jumps Over The Lazy Dog"], output = 43 *)
Example test_strlen_fox : strlen_spec "The Quick Brown Fox Jumps Over The Lazy Dog" 43.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.