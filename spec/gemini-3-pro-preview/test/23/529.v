Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["hy         functoio"], output = 19 *)
Example test_strlen_1 : strlen_spec "hy         functoio" 19.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.