Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_98765432100_1000000000 : greatest_common_divisor_spec 98765432100 1000000000 100.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.