Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["    1tBrownsampBrownleLazy 1   "], output = 31 *)
Example test_strlen_complex : strlen_spec "    1tBrownsampBrownleLazy 1   " 31.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.