Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_1092387468_neg97 :
  multiply_spec_abs 1092387468 (-97) 56.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.