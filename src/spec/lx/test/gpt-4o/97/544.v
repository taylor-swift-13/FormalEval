Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_6784_neg987654 :
  multiply_spec_abs 6784 (-987654) 16.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.