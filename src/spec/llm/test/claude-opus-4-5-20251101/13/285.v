Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_987654320_1000000000 : greatest_common_divisor_spec 987654320 1000000000 80.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.