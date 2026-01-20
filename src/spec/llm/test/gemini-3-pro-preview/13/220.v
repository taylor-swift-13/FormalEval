Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_999999998_111111110 : greatest_common_divisor_spec 999999998 111111110 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.