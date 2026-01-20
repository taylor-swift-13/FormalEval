Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_1684168416840_987654321 : greatest_common_divisor_spec 1684168416840 987654321 3.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.