Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_long : strlen_spec "123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789" 99.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.