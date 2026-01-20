Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111111_111111112 : greatest_common_divisor_spec 111111111 111111112 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.