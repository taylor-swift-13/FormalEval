Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus987656_minus987656 :
  multiply_spec_abs (-987656) (-987656) 36.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.