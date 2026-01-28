Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Th!s40ls !n 1t
" 15.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.