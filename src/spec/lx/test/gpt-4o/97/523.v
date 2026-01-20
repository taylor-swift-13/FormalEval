Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_9876543208_neg975312469 :
  multiply_spec_abs 9876543208 (-975312469) 72.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.