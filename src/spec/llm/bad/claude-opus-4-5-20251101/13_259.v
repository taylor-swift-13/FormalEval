Require Import ZArith.
Require Import Znumtheory.

Open Scope Z_scope.

Definition greatest_common_divisor_spec (a : Z) (b : Z) (result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_987654323_1684168416841 : greatest_common_divisor_spec 987654323 1684168416841 1.
Proof.
  unfold greatest_common_divisor_spec.
  native_cast_no_check (eq_refl 1).
Qed.