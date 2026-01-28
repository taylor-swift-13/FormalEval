Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "off
abcdefgjklmnopqrstuvwxyzfoivife" 35.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.