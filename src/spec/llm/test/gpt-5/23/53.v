Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogQyadEb" 219.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "G1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quick brown fox jumps over theThe quick brown fox jumps overq the lazy dog lazy Thisthree
four
fiveracter dogQyadEb") = 219%Z.
Proof.
  simpl.
  reflexivity.
Qed.