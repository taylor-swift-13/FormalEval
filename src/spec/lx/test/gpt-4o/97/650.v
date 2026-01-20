Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus12_1092387465 :
  multiply_spec_abs (-12) 1092387465 10.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.