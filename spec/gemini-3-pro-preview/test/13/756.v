Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654321_999999998 : greatest_common_divisor_spec 987654321 999999998 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.