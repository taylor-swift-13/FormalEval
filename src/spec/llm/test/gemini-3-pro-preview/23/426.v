Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["str1nb0lse"], output = 10 *)
Example test_strlen_complex : strlen_spec "str1nb0lse" 10.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.