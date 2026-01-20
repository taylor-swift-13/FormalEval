Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_long : strlen_spec "MNhqThe CQuicJumpsk Browno Fox Jumps Over The BrownLazy DogmCV" 62.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.