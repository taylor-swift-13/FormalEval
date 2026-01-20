Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_1092387464_neg975312471 :
  multiply_spec_abs 1092387464 (-975312471) 4.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.