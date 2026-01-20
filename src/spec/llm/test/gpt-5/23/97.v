Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "Hellone
twot
three
four
fivo, WoG1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quirck brown fox jumps over theThe quick by Thisthree
four
fiveracter dogQyadEborlod!" 221.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "Hellone
twot
three
four
fivo, WoG1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5NDKThe quirck brown fox jumps over theThe quick by Thisthree
four
fiveracter dogQyadEborlod!") = 221%Z.
Proof.
  simpl.
  reflexivity.
Qed.