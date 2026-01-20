Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_246813583_246813582 :
  multiply_spec_abs 246813583 246813582 6.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.