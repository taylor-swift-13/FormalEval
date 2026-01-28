Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (string : string) (length : nat) : Prop :=
  length = String.length string.

Example test_strlen_complex : strlen_spec "Th!s40ls !n 1This is a sample string    This Dàèìòù4áéíóúýâêîôûãñõäëïöüÿçgogis a samplt1t            etto string to LqNCZAtest the func Theon           to test the functi           àèìòùáéíóúýâêîQckôûãñõäëïöüÿçnt
" 265.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.