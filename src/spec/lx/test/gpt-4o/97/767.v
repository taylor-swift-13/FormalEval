Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_1092387466_246813580 :
  multiply_spec_abs 1092387466 246813580 0.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.