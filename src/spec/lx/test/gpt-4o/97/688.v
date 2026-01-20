Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg17_2938475611 :
  multiply_spec_abs (-17) 2938475611 7.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.