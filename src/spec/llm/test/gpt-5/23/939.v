Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.
Open Scope string_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition s_case : string :=
  "  te      1t  sThe    s tt"
  ++ String.String (Ascii.ascii_of_nat 13) String.EmptyString
  ++ " "
  ++ String.String (Ascii.ascii_of_nat 10) String.EmptyString
  ++ "1"
  ++ String.String (Ascii.ascii_of_nat 13) String.EmptyString
  ++ " Foxstr1str1ngng".

Example strlen_spec_case: strlen_spec s_case 47.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length s_case) = 47%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.