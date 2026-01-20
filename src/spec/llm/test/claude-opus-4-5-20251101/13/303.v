Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_1684168416842_108 : greatest_common_divisor_spec 1684168416842 108 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.