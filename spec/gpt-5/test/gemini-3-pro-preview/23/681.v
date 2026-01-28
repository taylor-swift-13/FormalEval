Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "MNhqThe CQuick Brown Fox oJutesttmps Oqver The BrownLazy DogmCV" 63.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.