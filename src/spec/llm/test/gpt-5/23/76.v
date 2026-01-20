Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "TheHello,The quick brown fox jumps over the lazy Thisthree
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

Example strlen_test_long_Z: Z.of_nat (String.length "TheHello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld! quick broThis string Thas a 
 newline characterwn fox jumps over theone
twota
thrThis is a long string that has many characters in itee
four
five dog") = 241%Z.
Proof.
  simpl.
  reflexivity.
Qed.