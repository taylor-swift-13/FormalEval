Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNe CQuick Brown Fox oJumps Over The BrownLazy DogmCV" 53.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.