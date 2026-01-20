Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_case: strlen_spec "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts" 118.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_case_Z: Z.of_nat (String.length "BrowMNhqThe CQuick Brown Fwox Jumpes Over The BrownLazey DogmCVnsampBrownleLazyhTiTh!s 1s 4 str1ng w1th 5ymb0ls !n 1ts") = 118%Z.
Proof.
  simpl.
  reflexivity.
Qed.