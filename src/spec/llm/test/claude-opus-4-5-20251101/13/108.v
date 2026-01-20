Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_123456789_987654321 : greatest_common_divisor_spec 123456789 987654321 9.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.