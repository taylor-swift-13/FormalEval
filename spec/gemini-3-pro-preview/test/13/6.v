Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_98_56 : greatest_common_divisor_spec 98 56 14.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.