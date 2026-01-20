Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654320_987654320 : greatest_common_divisor_spec 987654320 987654320 987654320.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.