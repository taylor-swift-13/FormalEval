Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec (String.append "  te      1t  sThe    s tt"
  (String (Ascii.ascii_of_nat 13)
     (String (Ascii.ascii_of_nat 10)
        (String (Ascii.ascii_of_nat 32)
           (String (Ascii.ascii_of_nat 13)
              " Foxstr1str1ngng"))))) 46.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length (String.append "  te      1t  sThe    s tt"
  (String (Ascii.ascii_of_nat 13)
     (String (Ascii.ascii_of_nat 10)
        (String (Ascii.ascii_of_nat 32)
           (String (Ascii.ascii_of_nat 13)
              " Foxstr1str1ngng")))))) = 46%Z.
Proof.
  simpl.
  reflexivity.
Qed.