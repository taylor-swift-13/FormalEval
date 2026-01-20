Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_string_with_symbols : strlen_spec "Th!s 1s 4 str1ng wtest5ymb0ls !n 1t
" 36.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.