Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_6786_minus_975312468 :
  multiply_spec_abs 6786 (-975312468) 48.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.