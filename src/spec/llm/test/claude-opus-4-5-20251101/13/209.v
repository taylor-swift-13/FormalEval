Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_123456790_987654320 : greatest_common_divisor_spec 123456790 987654320 123456790.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.