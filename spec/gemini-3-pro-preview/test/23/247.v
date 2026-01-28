Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["RLkion"], output = 6%Z *)
Example test_strlen_RLkion : strlen_spec "RLkion" 6.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.