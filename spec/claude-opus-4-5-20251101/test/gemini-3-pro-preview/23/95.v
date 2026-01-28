Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 neThe quick brown f ox jumps over the lazygwline character5" 137.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.