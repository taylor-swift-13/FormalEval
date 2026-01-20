Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition whitespace_string : string :=
  String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 13)
  (String (Ascii.ascii_of_nat 10)
  (String (Ascii.ascii_of_nat 13)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32) EmptyString))))))).

Example strlen_spec_whitespace: strlen_spec whitespace_string 8.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_whitespace_Z: Z.of_nat (String.length whitespace_string) = 8%Z.
Proof.
  simpl.
  reflexivity.
Qed.