Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["ab"], output = 2 *)
Example test_strlen_2 : strlen_spec "ab" 2.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.