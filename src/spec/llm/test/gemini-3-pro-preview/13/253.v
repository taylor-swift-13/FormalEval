Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_98765432099_999999999 : greatest_common_divisor_spec 98765432099 999999999 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.