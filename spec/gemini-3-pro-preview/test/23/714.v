Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["ThT     testt1t 1 The    iMNhq1TMNMNhqThehe"], output = 43 *)
Example test_strlen_complex : strlen_spec "ThT     testt1t 1 The    iMNhq1TMNMNhqThehe" 43.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.