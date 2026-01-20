Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_967_108 : greatest_common_divisor_spec 967 108 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.