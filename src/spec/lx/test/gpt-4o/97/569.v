Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus_9876543211_minus_10 :
  multiply_spec_abs (-9876543211) (-10) 0.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.