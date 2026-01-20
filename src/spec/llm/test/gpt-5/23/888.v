Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example strlen_spec_new: strlen_spec "BrownLazMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sastr1str1ngnsgmple string to test th e functionCdV The BrownLazy DogmCVys" 132.
Proof.
  unfold strlen_spec.
  simpl.
  reflexivity.
Qed.

Example strlen_test_new_Z: Z.of_nat (String.length "BrownLazMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sastr1str1ngnsgmple string to test th e functionCdV The BrownLazy DogmCVys") = 132%Z.
Proof.
  simpl.
  reflexivity.
Qed.