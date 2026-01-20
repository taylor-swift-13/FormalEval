Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition test_string : string :=
  String.append " This striThis is a long string that has many characters in itng has a "
    (String.append (String (Ascii.ascii_of_nat 10) EmptyString) " newline character").

Example strlen_spec_long: strlen_spec test_string 90.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_long_Z: Z.of_nat (String.length test_string) = 90%Z.
Proof.
  simpl.
  reflexivity.
Qed.