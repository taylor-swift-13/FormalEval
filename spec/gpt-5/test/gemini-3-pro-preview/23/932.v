Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_non_empty : strlen_spec "aCQuDogmCVnsampBrownleLazyickzys" 32.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.