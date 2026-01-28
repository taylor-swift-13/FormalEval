Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_long : strlen_spec "The quick brown fox11234567890 jumps over the lazy This striThis is aaracter dog" 80.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.