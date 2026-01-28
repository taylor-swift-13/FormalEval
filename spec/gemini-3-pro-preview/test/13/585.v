Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_111111109_105 : greatest_common_divisor_spec 111111109 105 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.