Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCV
hqmCV" 65.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.