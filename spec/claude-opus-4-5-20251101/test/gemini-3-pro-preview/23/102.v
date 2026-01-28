Require Import Coq.Strings.String.
Require Import Coq.Arith.PeanoNat.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example test_strlen_complex : strlen_spec "Testing te stingone
twot
thrThis is a long strinThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogg that has many characters in itee
four
five 123" 209.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.