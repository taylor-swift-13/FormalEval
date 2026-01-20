Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_6789_neg9876543211 :
  multiply_spec_abs 6789 (-9876543211) 9.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.