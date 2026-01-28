Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_99999999_999999998 : greatest_common_divisor_spec 99999999 999999998 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.