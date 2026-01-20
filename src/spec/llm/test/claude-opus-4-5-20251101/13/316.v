Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_1000000001_234567888 : greatest_common_divisor_spec 1000000001 234567888 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.