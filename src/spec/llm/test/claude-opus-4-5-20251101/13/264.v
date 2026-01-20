Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_987654318_108 : greatest_common_divisor_spec 987654318 108 6.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.