Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_100000000_123456788 : greatest_common_divisor_spec 100000000 123456788 4.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.