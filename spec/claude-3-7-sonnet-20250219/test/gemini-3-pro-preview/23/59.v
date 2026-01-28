Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Hello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld!" 88.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.