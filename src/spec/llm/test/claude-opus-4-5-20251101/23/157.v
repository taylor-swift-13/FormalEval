Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_test_string : strlen_spec "Th!s 1s 4 str1ng wtest5ymb0ls !nsampleto 1t
" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.