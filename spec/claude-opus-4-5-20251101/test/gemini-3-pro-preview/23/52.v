Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "The quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dog" 113.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.