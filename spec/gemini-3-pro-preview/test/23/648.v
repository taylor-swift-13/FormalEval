Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation *)
Open Scope string_scope.

(* Test case: input = ["CQuicJstrOveringumpsk"], output = 21 *)
Example test_strlen_complex : strlen_spec "CQuicJstrOveringumpsk" 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.