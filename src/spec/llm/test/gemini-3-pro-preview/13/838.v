Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_987654320_192 : greatest_common_divisor_spec 987654320 192 16.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.