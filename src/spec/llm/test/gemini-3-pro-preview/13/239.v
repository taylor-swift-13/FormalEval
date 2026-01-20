Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_greatest_common_divisor : greatest_common_divisor_spec 234567888 1234567890 6.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.