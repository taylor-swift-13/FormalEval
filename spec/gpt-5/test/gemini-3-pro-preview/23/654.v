Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "ThhT    1t 1 The    i" 21.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.