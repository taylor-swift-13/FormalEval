Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_neg_9876543209_neg_8 :
  multiply_spec_abs (-9876543209) (-8) 72.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.