Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_966_111111112 : greatest_common_divisor_spec 966 111111112 14.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.