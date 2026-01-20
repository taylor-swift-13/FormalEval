Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["functoion"], output = 9 *)
Example test_strlen_functoion : strlen_spec "functoion" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.