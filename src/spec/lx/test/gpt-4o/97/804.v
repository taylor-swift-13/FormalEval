Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_6791_1234567895 :
  multiply_spec_abs 6791 1234567895 5.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.