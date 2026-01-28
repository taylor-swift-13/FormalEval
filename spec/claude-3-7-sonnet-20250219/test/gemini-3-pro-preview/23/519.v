Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "  Th!s 1s 4 st1   

wwtest5ymb40ls    r1ng wtest5nymb0ls !nsampleto 1t
" 71.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.