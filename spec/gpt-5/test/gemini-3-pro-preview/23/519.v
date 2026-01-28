Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_case1 : strlen_spec "  Th!s 1s 4 st1   

wwtest5ymb40ls    r1ng wtest5nymb0ls !nsampleto 1t
" 71.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.