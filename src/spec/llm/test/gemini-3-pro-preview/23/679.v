Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk BrowMNhqmn Fox Jumps OverThis  to test t" 60.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.