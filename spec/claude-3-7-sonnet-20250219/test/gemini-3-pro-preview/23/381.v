Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_case1 : strlen_spec "  Th!s 1s 4 str1ng wtest5nymb0ls !nsampleto 1t
" 47.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.