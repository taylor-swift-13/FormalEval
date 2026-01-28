Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_106_1684168416840 : greatest_common_divisor_spec 106 1684168416840 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.