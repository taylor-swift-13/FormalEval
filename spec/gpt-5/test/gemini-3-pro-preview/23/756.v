Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_long : strlen_spec "MNhqThe CQuicJumpsk Browno Fox Jumps Over The BrownLazy DogmCV" 62.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.