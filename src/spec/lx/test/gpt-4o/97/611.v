Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_246813580_246813579 :
  multiply_spec_abs 246813580 246813579 0.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.