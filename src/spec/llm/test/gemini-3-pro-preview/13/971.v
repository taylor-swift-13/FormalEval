Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_3699636_28 : greatest_common_divisor_spec 3699636 28 4.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.