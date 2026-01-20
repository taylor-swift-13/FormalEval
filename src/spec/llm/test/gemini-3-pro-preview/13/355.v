Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111110_418 : greatest_common_divisor_spec 111111110 418 22.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.