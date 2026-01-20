Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "Tish!  TTh!s40lsh!s 1s 4 str1ng wtest5ymb0lse !n 1t
         " 61.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "Tish!  TTh!s40lsh!s 1s 4 str1ng wtest5ymb0lse !n 1t
         ") = 61%Z.
Proof.
  simpl.
  reflexivity.
Qed.