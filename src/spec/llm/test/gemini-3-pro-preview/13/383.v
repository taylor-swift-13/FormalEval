Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_1000000002_1000000000 : greatest_common_divisor_spec 1000000002 1000000000 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.