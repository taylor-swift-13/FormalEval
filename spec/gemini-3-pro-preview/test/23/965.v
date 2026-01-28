Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["hThT     testt1t 1 The    iMNhq1TMNMNhqThehe"], output = 44 *)
Example test_strlen_1 : strlen_spec "hThT     testt1t 1 The    iMNhq1TMNMNhqThehe" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.