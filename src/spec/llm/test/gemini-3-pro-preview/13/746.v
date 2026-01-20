Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_420_123456790 : greatest_common_divisor_spec 420 123456790 10.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.