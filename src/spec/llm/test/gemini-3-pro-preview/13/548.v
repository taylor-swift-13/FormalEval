Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_100000000_1684168416846 : greatest_common_divisor_spec 100000000 1684168416846 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.