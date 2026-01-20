Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string :=
  String (Ascii.ascii_of_nat 66)
  (String (Ascii.ascii_of_nat 114)
  (String (Ascii.ascii_of_nat 76)
  (String (Ascii.ascii_of_nat 111)
  (String (Ascii.ascii_of_nat 119)
  (String (Ascii.ascii_of_nat 110)
  (String (Ascii.ascii_of_nat 76)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 13)
  (String (Ascii.ascii_of_nat 10)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 97)
  (String (Ascii.ascii_of_nat 122)
  (String (Ascii.ascii_of_nat 121)
  (String (Ascii.ascii_of_nat 115)
  EmptyString))))))))))))))))))).

Example strlen_spec_case: strlen_spec test_string 20.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length test_string) = 20%Z.
Proof.
  simpl.
  reflexivity.
Qed.