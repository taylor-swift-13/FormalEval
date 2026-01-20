Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintoTh!s 1s 4 str1ng w1th 5ymb0ls !n 1testMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVt1tt Over The TBrowMNhqmnrownisgmCVg to test the function
gmCV" 237.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "MNhqThe CQuick Brown hFox Jumps Over The BrownLazy DoMNhThis is a sample strintoTh!s 1s 4 str1ng w1th 5ymb0ls !n 1testMNhqThe CQuick Brown Fox Jumpes Over The BrownLazy DogmCVt1tt Over The TBrowMNhqmnrownisgmCVg to test the function
gmCV") = 237%Z.
Proof.
  simpl.
  reflexivity.
Qed.