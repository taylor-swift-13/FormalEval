Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_123456790_1684168416838 : greatest_common_divisor_spec 123456790 1684168416838 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.