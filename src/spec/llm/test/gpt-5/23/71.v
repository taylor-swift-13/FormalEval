Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "TheHello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld! quick broThis string Thas a 
 newline characterwn fox jumps over the lazy Thisthree
four
fiveracter dog" 195.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "TheHello,The quick brown fox jumps over the lazy Thisthree
four
fiveracter dog Woo12345rld! quick broThis string Thas a 
 newline characterwn fox jumps over the lazy Thisthree
four
fiveracter dog") = 195%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.