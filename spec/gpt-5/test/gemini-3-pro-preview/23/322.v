Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_ps1ss : strlen_spec "ps1ss" 5.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.