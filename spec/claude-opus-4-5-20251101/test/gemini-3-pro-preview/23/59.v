Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat. (* Replaces incorrect Coq.Numbers.Natural.Peano.NPeano *)

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "Hello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld!" 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.