Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_195_98765432102 : greatest_common_divisor_spec 195 98765432102 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.