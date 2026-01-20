Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec "1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5" 96.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length "1234 This sitriThis is a long string that has many characters in itng has a 
 newline character5") = 96%Z.
Proof.
  simpl.
  reflexivity.
Qed.