Require Import Coq.Strings.String.
Require Import Coq.Numbers.Natural.Peano.NPeano.

Definition strlen_spec (s : string) (result : nat) : Prop :=
  result = String.length s.

Example strlen_long_string : strlen_spec "TheHello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld! quick broThis string Thas a 
 newline characterwn fox jumps over theone
twota
thrThis is a long string that has many characters in itee
four
five dog" 241.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.