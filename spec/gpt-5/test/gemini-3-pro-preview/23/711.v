Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThe CQuDogmCVnsampBrownleLazyick Brown Fox oJutesttmps Oqver The BrownLazy DogmCV" 85.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.