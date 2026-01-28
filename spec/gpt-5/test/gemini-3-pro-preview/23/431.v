Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "  Th!s 1s 4 st1r1ng wtest5nymb0ls !nsampleto 1t
" 48.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.