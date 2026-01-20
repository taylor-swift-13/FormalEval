Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Example strlen_spec_multiline: strlen_spec ("one" ++ nl ++ "twot" ++ nl ++ "thrThis is a long string that has  many characters in itee" ++ nl ++ "four" ++ nl ++ "five") 77.
Proof.
  unfold strlen_spec.
  unfold nl.
  simpl.
  reflexivity.
Qed.

Example strlen_test_multiline_Z: Z.of_nat (String.length ("one" ++ nl ++ "twot" ++ nl ++ "thrThis is a long string that has  many characters in itee" ++ nl ++ "four" ++ nl ++ "five")) = 77%Z.
Proof.
  unfold nl.
  simpl.
  reflexivity.
Qed.