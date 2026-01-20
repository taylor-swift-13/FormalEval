Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (res : nat) : Prop :=
  res = String.length s.

Open Scope string_scope.

Example test_strlen_complex : strlen_spec "Th    This iTh!s 1s RL4 str1ng wtest5ymb0l !n 1t
s a sample TTetnstrinisg Jumpet   

wtest5ymb40ls    t
" 104.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.