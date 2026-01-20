Require Import Coq.Strings.String.

(* Specification definition provided in the prompt *)
Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

(* Enable string notation for "" *)
Open Scope string_scope.

Example test_strlen_custom : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test th e functionCdV The BrownLazy DogmCV" 109.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.