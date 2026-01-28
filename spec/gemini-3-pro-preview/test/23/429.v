Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

(* Test case: input = ["samplt1t"], output = 8 *)
Example test_strlen_sample : strlen_spec "samplt1t" 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.