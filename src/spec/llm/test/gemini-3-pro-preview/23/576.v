Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["aOwtest5nymb0lsver"], output = 18 *)
Example test_strlen_1 : strlen_spec "aOwtest5nymb0lsver" 18.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.