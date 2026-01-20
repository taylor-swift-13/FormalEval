Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["1s"], output = 2 *)
Example test_strlen_1s : strlen_spec "1s" 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.