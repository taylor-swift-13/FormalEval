Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_complex : strlen_spec "Th!s 1s 4 stTheTer1ng wtest5ymb0lse !n 1t
" 42.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.