Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec " Th!s 1s 4 str1ng w1thn 5ymb0ls !n 1t Over The TTBrownisgmCV" 60.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length " Th!s 1s 4 str1ng w1thn 5ymb0ls !n 1t Over The TTBrownisgmCV") = 60%Z.
Proof.
  compute.
  reflexivity.
Qed.