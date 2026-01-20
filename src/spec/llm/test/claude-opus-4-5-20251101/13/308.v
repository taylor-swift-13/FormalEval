Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_123456788_987654322 : greatest_common_divisor_spec 123456788 987654322 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.