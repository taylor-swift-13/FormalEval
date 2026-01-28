Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["stgrsr1ng"], output = 9 *)
Example test_strlen_stgrsr1ng : strlen_spec "stgrsr1ng" 9.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.