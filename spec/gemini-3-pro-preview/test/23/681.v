Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "MNhqThe CQuick Brown Fox oJutesttmps Oqver The BrownLazy DogmCV" 63.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.