Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_alphabet : strlen_spec "abcdefghijklmnopqrstuvwxyz" 26.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.