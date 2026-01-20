Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_custom : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sample string to test the function The BrownLazy DogmCV" 105.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.