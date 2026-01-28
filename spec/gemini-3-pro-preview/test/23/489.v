Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["Tsh!s"], output = 5 *)
Example test_strlen_Tsh_s : strlen_spec "Tsh!s" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.