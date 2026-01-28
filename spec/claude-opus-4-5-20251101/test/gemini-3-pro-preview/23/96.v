Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "912345667890The quick brown fox jumps over the lazy This striThis is aaracter dogM" 82.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.