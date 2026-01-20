Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_999999999_111111110 : greatest_common_divisor_spec 999999999 111111110 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.