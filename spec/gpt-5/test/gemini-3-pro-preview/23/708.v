Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "MNhqThe CQuicJumpsk Brown Foxstr1str1ngng Jumps OverThis is a sample string to test thCV" 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.