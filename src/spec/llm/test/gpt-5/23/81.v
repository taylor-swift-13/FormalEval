Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_long: strlen_spec
  (String.append
    "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a "%string
    (String (Ascii.ascii_of_nat 10)
            " newline character5rstuvwxyz"%string))
  141.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length
  (String.append
    "abcdefghijklTest1iTng testing 123mnopq1234 This striThis is a long string that has many characters in itnghas a "%string
    (String (Ascii.ascii_of_nat 10)
            " newline character5rstuvwxyz"%string))) = 141%Z.
Proof.
  simpl.
  reflexivity.
Qed.