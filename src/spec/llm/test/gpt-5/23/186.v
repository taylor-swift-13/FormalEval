Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition s : string :=
  String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 10)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 49)
  (String (Ascii.ascii_of_nat 115)
  (String (Ascii.ascii_of_nat 32)
  (String (Ascii.ascii_of_nat 32) EmptyString)))))))))).

Example strlen_spec_spaces_newline_1s: strlen_spec s 11.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_spaces_newline_1s_Z: Z.of_nat (String.length s) = 11%Z.
Proof.
  simpl.
  reflexivity.
Qed.