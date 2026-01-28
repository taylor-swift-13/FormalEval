Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_10_123456789 : greatest_common_divisor_spec 10 123456789 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.