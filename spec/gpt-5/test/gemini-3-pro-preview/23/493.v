Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_RL4 : strlen_spec "RL4" 3.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.