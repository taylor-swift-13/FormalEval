Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["1This"], output = 5 *)
Example test_strlen_1This : strlen_spec "1This" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.