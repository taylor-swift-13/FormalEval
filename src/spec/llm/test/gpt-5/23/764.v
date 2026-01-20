Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_test: strlen_spec "Th!s 1s 4 str1ng w1th 5ymb0ls !n 1t Over The TrownisgmCV" 56.
Proof.
  unfold strlen_spec.
  vm_compute.
  reflexivity.
Qed.

Example strlen_test_Z: Z.of_nat (String.length "Th!s 1s 4 str1ng w1th 5ymb0ls !n 1t Over The TrownisgmCV") = 56%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.