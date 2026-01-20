Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_12_999999999 : greatest_common_divisor_spec 12 999999999 3.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.