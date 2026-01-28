Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case : strlen_spec "Th    This iTh!s 1s RL4 str1ng wtest5ymb0l !n 1t
s a sample TTetnstrinisg Jumpet   

wtest5ymb40ls    t
" 104.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.