Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_98765432099_108 : greatest_common_divisor_spec 98765432099 108 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.