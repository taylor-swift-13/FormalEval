Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus123458_2938475609 :
  multiply_spec_abs (-123458) 2938475609 72.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.