Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "Th    This is a sample TTetnstrinisg Jumpeto test the function           !s40ls !n 1t
" 86.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.