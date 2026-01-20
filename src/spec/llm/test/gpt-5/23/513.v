Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case1: strlen_spec
  (String.append "   "
     (String (Ascii.ascii_of_nat 10)
        (String.append "hy    This is a sample strinisg to ttest the fuunction          NcJH"
           (String (Ascii.ascii_of_nat 10) "  string"))))
  81.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case1_Z: Z.of_nat (String.length
  (String.append "   "
     (String (Ascii.ascii_of_nat 10)
        (String.append "hy    This is a sample strinisg to ttest the fuunction          NcJH"
           (String (Ascii.ascii_of_nat 10) "  string"))))) = 81%Z.
Proof.
  simpl.
  reflexivity.
Qed.