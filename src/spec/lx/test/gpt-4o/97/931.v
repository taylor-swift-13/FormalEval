Require Import ZArith.
Open Scope Z_scope.

Definition multiply_spec_abs (a b r : Z) : Prop :=
  r = (Z.abs a mod 10) * (Z.abs b mod 10).

Example multiply_test_1234567896_987654 :
  multiply_spec_abs 1234567896 987654 24.
Proof.
  unfold multiply_spec_abs.
  simpl.
  reflexivity.
Qed.