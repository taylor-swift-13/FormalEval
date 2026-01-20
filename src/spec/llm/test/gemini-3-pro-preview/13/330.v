Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_108_98765432100 : greatest_common_divisor_spec 108 98765432100 36.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.