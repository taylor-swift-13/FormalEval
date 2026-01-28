Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_1000000000_100000004 : greatest_common_divisor_spec 1000000000 100000004 4.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.