Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen : strlen_spec "MNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCV" 59.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.