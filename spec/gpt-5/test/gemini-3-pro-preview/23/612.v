Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk Brown Fox Jumps Over The BrownLazy DogmCV" 61.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.