Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_965_98765432100 : greatest_common_divisor_spec 965 98765432100 5.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.