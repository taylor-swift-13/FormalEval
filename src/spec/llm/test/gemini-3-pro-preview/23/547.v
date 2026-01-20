Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["kRLkion"], output = 7 *)
Example test_strlen_kRLkion : strlen_spec "kRLkion" 7.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.