Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_1684168416840_1684168416842 : greatest_common_divisor_spec 1684168416840 1684168416842 2.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.