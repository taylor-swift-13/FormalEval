Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_191_1684168416842 : greatest_common_divisor_spec 191 1684168416842 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.