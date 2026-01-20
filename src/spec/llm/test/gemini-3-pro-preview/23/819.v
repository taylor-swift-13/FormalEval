Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["TTBr ownis   "], output = 13 *)
Example test_strlen_complex : strlen_spec "TTBr ownis   " 13.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.