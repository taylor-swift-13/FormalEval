Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "BrownLazMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test th e functionCdV The BrownLazy DogmCVys" 119.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.