Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus_987657_2938475609 :
  multiply_spec_abs (-987657) 2938475609 63.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.