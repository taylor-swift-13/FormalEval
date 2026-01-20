Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_minus_975312469_246813579 :
  multiply_spec_abs (-975312469) 246813579 81.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.