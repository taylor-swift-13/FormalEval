Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example gcd_test_3_7 : greatest_common_divisor_spec 3 7 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.