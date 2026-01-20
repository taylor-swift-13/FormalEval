Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654324_987654323 : greatest_common_divisor_spec 987654324 987654323 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.