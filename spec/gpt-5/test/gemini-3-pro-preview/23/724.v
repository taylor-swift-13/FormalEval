Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_tVhCV : strlen_spec "tVhCV" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.