Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_98765432100_966 : greatest_common_divisor_spec 98765432100 966 6.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.