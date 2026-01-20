Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_6788_neg975312471 :
  multiply_spec_abs 6788 (-975312471) 8.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.