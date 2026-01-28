Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["Do      The    g"], output = 16 *)
Example test_strlen_spaces : strlen_spec "Do      The    g" 16.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.