Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "912345667890The quick brown fox jumps over the lazy This striThis is aaracter dogM" 82.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.