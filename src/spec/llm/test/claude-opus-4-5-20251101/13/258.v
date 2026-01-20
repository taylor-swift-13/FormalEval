Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_1000000002_1000000002 : greatest_common_divisor_spec 1000000002 1000000002 1000000002.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.