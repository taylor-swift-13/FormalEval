Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus100_1092387464 :
  multiply_spec_abs (-100) 1092387464 0.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.