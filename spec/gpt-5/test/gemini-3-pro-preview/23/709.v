Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_custom : strlen_spec "leOvMNhqThe CQuick Brown Fox oJumps Over The BrownLazy DogmCVering" 66.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.