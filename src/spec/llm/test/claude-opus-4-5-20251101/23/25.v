Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_quick_brown_fox : strlen_spec "The quick brown f ox jumps over the lazy dog" 44.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.