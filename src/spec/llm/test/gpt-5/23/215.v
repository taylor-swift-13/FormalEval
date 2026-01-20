Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Definition nl : string := String (Ascii.ascii_of_nat 10) EmptyString.

Definition test_string : string :=
  String.append
    (String.append "   " nl)
    (String.append
      (String.append "hy    This is a sample strinisg to test the fuunction          NcJH" nl)
      "  string").

Example strlen_spec_case: strlen_spec test_string 80.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length test_string) = 80%Z.
Proof.
  simpl.
  reflexivity.
Qed.