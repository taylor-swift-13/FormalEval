Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["r1ng"], output = 4 *)
Example test_strlen_r1ng : strlen_spec "r1ng" 4.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.