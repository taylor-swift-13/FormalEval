Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111111_999999998 : greatest_common_divisor_spec 111111111 999999998 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.