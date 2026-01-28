Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_30_111111111 : greatest_common_divisor_spec 30 111111111 3.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.