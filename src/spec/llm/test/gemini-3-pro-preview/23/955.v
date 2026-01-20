Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "leOvMNhqThe CQuick Brown Fox oJumps Ovepr The BrownLazy DogmCVering" 67.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.