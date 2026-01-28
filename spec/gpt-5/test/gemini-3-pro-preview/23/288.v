Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "Th    This is a sample TTetnstrinisg to test the function           !s40ls !n 1t
" 81.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.