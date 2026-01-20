Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_9876543211_neg17 :
  multiply_spec_abs 9876543211 (-17) 7.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.