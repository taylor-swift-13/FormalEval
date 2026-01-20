Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.
Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec ("     str1ng 1t  The    This is a samThT    1sampLazylet i1 The  MNhqThe CuQuicJumpBsk Brown Fo    " ++ String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) EmptyString) ++ "   xstr1str1ngng Jumps OverThis is a sample string to test thCVt the function") 177.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length ("     str1ng 1t  The    This is a samThT    1sampLazylet i1 The  MNhqThe CuQuicJumpBsk Brown Fo    " ++ String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) EmptyString) ++ "   xstr1str1ngng Jumps OverThis is a sample string to test thCVt the function")) = 177%Z.
Proof.
  simpl.
  reflexivity.
Qed.