Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_234567888_234567888 : greatest_common_divisor_spec 234567888 234567888 234567888.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.