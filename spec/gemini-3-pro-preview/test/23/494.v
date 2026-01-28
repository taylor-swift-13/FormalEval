Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["st1r1ng"], output = 7 *)
Example test_strlen_st1r1ng : strlen_spec "st1r1ng" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.