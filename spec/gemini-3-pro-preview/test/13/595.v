Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_greatest_common_divisor : greatest_common_divisor_spec 1684168416845 3699636 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.