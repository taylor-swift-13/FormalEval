Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["1234567890"], output = 10 *)
Example test_strlen_digits : strlen_spec "1234567890" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.