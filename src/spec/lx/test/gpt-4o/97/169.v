Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_2938475610_9876543210 :
  multiply_spec_abs 2938475610 9876543210 0.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.