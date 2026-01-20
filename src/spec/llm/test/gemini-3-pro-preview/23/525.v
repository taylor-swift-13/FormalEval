Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["thes"], output = 4 *)
Example test_strlen_thes : strlen_spec "thes" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.