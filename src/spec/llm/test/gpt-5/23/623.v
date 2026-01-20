Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_sample: strlen_spec (String.append (String.append "   This is a sample string to test the function" (String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) EmptyString))) "   z") 53.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_sample_Z: Z.of_nat (String.length (String.append (String.append "   This is a sample string to test the function" (String (Ascii.ascii_of_nat 10) (String (Ascii.ascii_of_nat 10) EmptyString))) "   z")) = 53%Z.
Proof.
  simpl.
  reflexivity.
Qed.