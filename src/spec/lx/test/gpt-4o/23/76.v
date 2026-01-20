Require Import String.

Definition Spec(input : string) (output : nat) : Prop :=
  output = length input.

Example strlen_test_long_string :
  Spec "TheHello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld! quick broThis string Thas a 
 newline characterwn fox jumps over theone
twota
thrThis is a long string that has many characters in itee
four
five dog" 241.
Proof.
  unfold Spec.
  simpl.
  reflexivity.
Qed.