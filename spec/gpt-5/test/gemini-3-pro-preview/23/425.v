Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Th!s 1s RL4 str1ng wtest5ymb0l !n 1t
" 37.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.