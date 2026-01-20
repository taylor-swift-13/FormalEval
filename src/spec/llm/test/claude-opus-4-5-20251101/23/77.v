Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "thrieeThe quick brown f ox jumps over the lazy dogThe quick brown fox jumps overq the lazy dog
four
five " 105.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.