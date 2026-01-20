Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_246813578_neg987657 :
  multiply_spec_abs 246813578 (-987657) 56.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.