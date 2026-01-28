Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["s"], output = 1 *)
Example test_strlen_s : strlen_spec "s" 1.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.