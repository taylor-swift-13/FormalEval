Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "The quick brown fox jumps over theThe quick brown fox jxumps overq the lazy dog lazy Thisthree
four
fiveracter dog" 114.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.