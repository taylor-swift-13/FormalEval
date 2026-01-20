Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition s : string :=
  String (Ascii.ascii_of_nat 238)
    (String (Ascii.ascii_of_nat 244)
    (String (Ascii.ascii_of_nat 251)
    (String (Ascii.ascii_of_nat 227)
    (String (Ascii.ascii_of_nat 241)
    (String (Ascii.ascii_of_nat 245)
    (String (Ascii.ascii_of_nat 228)
    (String (Ascii.ascii_of_nat 235)
    (String (Ascii.ascii_of_nat 239)
    (String (Ascii.ascii_of_nat 246)
    (String (Ascii.ascii_of_nat 252)
    (String (Ascii.ascii_of_nat 255)
    (String (Ascii.ascii_of_nat 231)
    (String (Ascii.ascii_of_nat 81)
    (String (Ascii.ascii_of_nat 70)
    (String (Ascii.ascii_of_nat 111)
    (String (Ascii.ascii_of_nat 81)
    (String (Ascii.ascii_of_nat 120)
    (String (Ascii.ascii_of_nat 117)
    (String (Ascii.ascii_of_nat 107)
    (String (Ascii.ascii_of_nat 121)
    (String (Ascii.ascii_of_nat 105)
    (String (Ascii.ascii_of_nat 99)
    (String (Ascii.ascii_of_nat 107)
    (String (Ascii.ascii_of_nat 121)
    (String (Ascii.ascii_of_nat 116)
    (String (Ascii.ascii_of_nat 104)
    (String (Ascii.ascii_of_nat 101)
      EmptyString))))))))))))))))))))))))))).

Example strlen_spec_unicode: strlen_spec s 28.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_unicode_Z: Z.of_nat (String.length s) = 28%Z.
Proof.
  simpl.
  reflexivity.
Qed.