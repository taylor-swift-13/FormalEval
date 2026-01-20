Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "Testing te stingone
twot
thrThis is a long strinThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogg that has many characters in itee
four
five 123" 209.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.