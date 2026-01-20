Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_21_20 : greatest_common_divisor_spec 21 20 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.