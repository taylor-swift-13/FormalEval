Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_1000000000_999999999 : greatest_common_divisor_spec 1000000000 999999999 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.