Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["!nn"], output = 3 *)
Example test_strlen_bang_nn : strlen_spec "!nn" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.