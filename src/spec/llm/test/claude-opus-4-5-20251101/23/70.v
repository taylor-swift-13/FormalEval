Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "G1The quick brown f ox jumps over the lazy dog234  has a 
 newline character5NDKQyadEb" 86.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.