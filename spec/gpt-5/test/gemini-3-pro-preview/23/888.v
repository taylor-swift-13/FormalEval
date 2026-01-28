Require Import Coq.Strings.String.

Definition strlen_spec (s : string) (n : nat) : Prop :=
  n = String.length s.

Example test_strlen_1 : strlen_spec "BrownLazMNhqThe CQuicJumpsk Brown Fox Jumps OverThis is a sastr1str1ngnsgmple string to test th e functionCdV The BrownLazy DogmCVys" 132.
Proof.
  unfold strlen_spec.
  reflexivity.
Qed.