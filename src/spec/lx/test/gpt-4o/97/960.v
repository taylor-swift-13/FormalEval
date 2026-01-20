Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus_975312467_1234567889 :
  multiply_spec_abs (-975312467) 1234567889 63.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.