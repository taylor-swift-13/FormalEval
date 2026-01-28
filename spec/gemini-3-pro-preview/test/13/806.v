Require Import Coq.ZArith.ZArith.
Open Scope Z_scope.

Definition greatest_common_divisor_spec (a b result : Z) : Prop :=
  result = Z.gcd a b.

Example test_gcd_999999999_111111109 : greatest_common_divisor_spec 999999999 111111109 1.
Proof.
  unfold greatest_common_divisor_spec.
  reflexivity.
Qed.