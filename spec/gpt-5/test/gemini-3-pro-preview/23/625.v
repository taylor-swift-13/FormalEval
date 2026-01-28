Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "ThT    1t 1 The    i" 20.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.